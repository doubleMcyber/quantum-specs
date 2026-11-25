/-
Copyright 2026 Marlon Moenius

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import LowerBounds.Grover.Defs
import Mathlib

/-!
# Unrolled loops approximate the library's semantics from below

The unrolled programs `(unroll M c).compile O` approximate the library's semantics of
`c.compile QProg.qAssign O` from below. Three facts are proved:
(1) every expectation of the unrolled program is monotone in `M` (`unroll_expect_mono`);
(2) it tends to the expectation of the original program (`unroll_expect_tendsto`);
(3) the expected cost of the unrolled program is at most that of the original (`unroll_cost_le`).

Route for (1) and (2): weakest preconditions. `Conv u v` says that the assertions `u M` increase to
`v` as seen by every expectation. It is preserved by `wp P` (through `expect_wp`), by the pointwise
`if`, by the diagonal `M ↦ wp (A M) (u M)` (double limit, `tendsto_diag`) and by the loop
unrollings `whileRecWP`. Route for (3): monotonicity in the state of `interp` and `expectedCost`
for the sublanguage `Good` (no `assign`, no `qSet`), and domination of both quantities by
induction on the circuit.
-/

open QuantumComputation.Specs Operator QMonad QMonad.Q ResourceCounting Filter
open scoped Matrix QHLExpectation ComplexOrder MatrixOrder ENNReal

namespace GroverLowerBound

/-! ### A double limit -/

lemma tendsto_diag {a : ℕ → ℕ → ℝ} {b : ℕ → ℝ} {L : ℝ}
    (h1 : ∀ m n, m ≤ n → ∀ k, a m k ≤ a n k)
    (h2 : ∀ m k l, k ≤ l → a m k ≤ a m l)
    (hin : ∀ m, Tendsto (a m) atTop (nhds (b m)))
    (hout : Tendsto b atTop (nhds L)) :
    Tendsto (fun m => a m m) atTop (nhds L) := by
  have hlub : ∀ m, IsLUB (Set.range (a m)) (b m) := fun m =>
    isLUB_of_tendsto_atTop (fun k l hkl => h2 m k l hkl) (hin m)
  have hbmono : Monotone b := by
    intro m n hmn
    refine (hlub m).2 ?_
    rintro _ ⟨k, rfl⟩
    exact (h1 m n hmn k).trans ((hlub n).1 ⟨k, rfl⟩)
  have hL : IsLUB (Set.range b) L := isLUB_of_tendsto_atTop hbmono hout
  have hdmono : Monotone (fun m => a m m) := fun m n hmn =>
    (h1 m n hmn m).trans (h2 n m n hmn)
  refine tendsto_atTop_isLUB hdmono ⟨?_, ?_⟩
  · rintro _ ⟨m, rfl⟩
    exact ((hlub m).1 ⟨m, rfl⟩).trans (hL.1 ⟨m, rfl⟩)
  · intro U hU
    refine hL.2 ?_
    rintro _ ⟨m, rfl⟩
    refine (hlub m).2 ?_
    rintro _ ⟨k, rfl⟩
    have := hU ⟨max m k, rfl⟩
    exact ((h1 m (max m k) (le_max_left _ _) k).trans
      (h2 (max m k) k (max m k) (le_max_right _ _))).trans this

/-! ### Convergence of assertions, seen through expectations -/

section conv

variable {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]

/-- The assertions `u M` increase with `M`, and their expectations in every state converge to the
expectation of `v`. -/
def Conv (u : ℕ → CQAssertion (Store Var) d) (v : CQAssertion (Store Var) d) : Prop :=
  Monotone u ∧ ∀ Δ : CQState (Store Var) d, Tendsto (fun M => 𝔼[Δ ⊨ u M]) atTop (nhds 𝔼[Δ ⊨ v])

lemma conv_const (w : CQAssertion (Store Var) d) : Conv (fun _ => w) w :=
  ⟨monotone_const, fun _ => tendsto_const_nhds⟩

lemma conv_wp {u : ℕ → CQAssertion (Store Var) d} {v : CQAssertion (Store Var) d}
    (h : Conv u v) (P : QProg Var d) : Conv (fun M => wp P (u M)) (wp P v) :=
  ⟨fun _ _ hmn => wp_mono P (h.1 hmn), fun Δ => by
    simp only [expect_wp]
    exact h.2 _⟩

lemma conv_ite (b : Store Var → Prop) [DecidablePred b]
    {u₁ u₂ : ℕ → CQAssertion (Store Var) d} {v₁ v₂ : CQAssertion (Store Var) d}
    (h₁ : Conv u₁ v₁) (h₂ : Conv u₂ v₂) :
    Conv (fun M => fun σ => if b σ then u₁ M σ else u₂ M σ)
      (fun σ => if b σ then v₁ σ else v₂ σ) := by
  refine ⟨fun m n hmn σ => ?_, fun Δ => ?_⟩
  · dsimp only
    split_ifs
    · exact h₁.1 hmn σ
    · exact h₂.1 hmn σ
  · simp_rw [expect_ite_partition b]
    exact (h₁.2 _).add (h₂.2 _)

/-- Diagonal of a family of programs: if `wp (A M)` converges to `wp F` on every postcondition
and `u` converges to `v`, then `wp (A M) (u M)` converges to `wp F v`. -/
lemma conv_wp_diag {A : ℕ → QProg Var d} {F : QProg Var d}
    (hA : ∀ Θ, Conv (fun M => wp (A M) Θ) (wp F Θ))
    {u : ℕ → CQAssertion (Store Var) d} {v : CQAssertion (Store Var) d} (hu : Conv u v) :
    Conv (fun M => wp (A M) (u M)) (wp F v) := by
  refine ⟨fun m n hmn => ?_, fun Δ => ?_⟩
  · exact ((wp_mono (A m)) (hu.1 hmn)).trans ((hA (u n)).1 hmn)
  · exact tendsto_diag (a := fun m k => 𝔼[Δ ⊨ wp (A m) (u k)])
      (b := fun m => 𝔼[Δ ⊨ wp (A m) v])
      (fun m n hmn k => expect_mono le_rfl ((hA (u k)).1 hmn))
      (fun m k l hkl => expect_mono le_rfl (wp_mono (A m) (hu.1 hkl)))
      (fun m => (conv_wp hu (A m)).2 Δ)
      ((hA v).2 Δ)

lemma whileRecWP_mono_body
    {body body' : CQAssertion (Store Var) d → CQAssertion (Store Var) d}
    (hb' : Monotone body') (hle : ∀ Θ, body Θ ≤ body' Θ)
    (b : Store Var → Prop) [DecidablePred b] (n : ℕ) (Θ : CQAssertion (Store Var) d) :
    whileRecWP body b n Θ ≤ whileRecWP body' b n Θ := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    intro σ
    simp only [whileRecWP]
    split_ifs
    · exact ((hle _).trans (hb' ih)) σ
    · exact le_rfl

/-- The loop case: unrollings of bodies `B M` that converge to `Fb` give unrollings (to depth `M`)
that converge to the library's `wp` of the loop. -/
lemma conv_while {B : ℕ → QProg Var d} {Fb : QProg Var d}
    (hB : ∀ Θ, Conv (fun M => wp (B M) Θ) (wp Fb Θ))
    (b : Store Var → Prop) [DecidablePred b] (Θ : CQAssertion (Store Var) d) :
    Conv (fun M => whileRecWP (wp (B M)) b M Θ) (wp (QProg.qWhile b Fb) Θ) := by
  have step : ∀ n, Conv (fun M => whileRecWP (wp (B M)) b n Θ) (whileRecWP (wp Fb) b n Θ) := by
    intro n
    induction n with
    | zero => exact conv_const (⊥ : CQAssertion (Store Var) d)
    | succ n ih =>
      exact conv_ite b (conv_wp_diag hB ih) (conv_const Θ)
  rw [wp_qWhile]
  refine ⟨fun m n hmn => ?_, fun Δ => ?_⟩
  · exact (whileRecWP_mono (wp_mono (B m)) b Θ hmn).trans
      (whileRecWP_mono_body (wp_mono (B n)) (fun Ψ => (hB Ψ).1 hmn) b n Θ)
  · exact tendsto_diag (a := fun n M => 𝔼[Δ ⊨ whileRecWP (wp (B M)) b n Θ])
      (b := fun n => 𝔼[Δ ⊨ whileRecWP (wp Fb) b n Θ])
      (fun m n hmn k => expect_mono le_rfl (whileRecWP_mono (wp_mono (B k)) b Θ hmn))
      (fun m k l hkl => expect_mono le_rfl
        (whileRecWP_mono_body (wp_mono (B l)) (fun Ψ => (hB Ψ).1 hkl) b m Θ))
      (fun n => (step n).2 Δ)
      (tendsto_expect_assertion_ωSup (whileRecWP.chain (wp Fb) (wp_mono Fb) b Θ) Δ)

end conv

/-! ### `wp` of an unrolled loop -/

section compile

variable {Var : Type} [DecidableEq Var] {Q w : ℕ}

lemma wp_compile_whileN (O : Unitary (2 ^ w)) (b : Store Var → Prop) [DecidablePred b]
    (B : LF Var Q w) (n : ℕ) (Θ : CQAssertion (Store Var) (2 ^ Q)) :
    wp ((LF.whileN b B n).compile O) Θ = whileRecWP (wp (B.compile O)) b n Θ := by
  induction n generalizing Θ with
  | zero => rfl
  | succ n ih =>
    funext σ
    simp only [LF.whileN, LF.compile, wp_qIf, wp_qSeq, wp_skip, whileRecWP, ih]

theorem convP (O : Unitary (2 ^ w))
    (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w) (Θ : CQAssertion (Store Var) (2 ^ Q)) :
    Conv (fun M => wp ((unroll M c).compile O) Θ) (wp (c.compile QProg.qAssign O) Θ) := by
  induction c generalizing Θ with
  | skip => exact conv_const _
  | step U => exact conv_const _
  | oracle r => exact conv_const _
  | measure v r => exact conv_const _
  | qIf b t f iht ihf =>
    exact conv_ite b (iht Θ) (ihf Θ)
  | qWhile b body ih =>
    have h := conv_while (B := fun M => (unroll M body).compile O)
      (Fb := body.compile QProg.qAssign O) ih b Θ
    rw [OracleDynamicCircuit.compile_qWhile]
    simpa only [unroll, wp_compile_whileN] using h
  | seq p₁ p₂ ih₁ ih₂ =>
    exact conv_wp_diag ih₁ (ih₂ Θ)

end compile

/-! ### Goals 1 and 2 -/

section main

variable {Var : Type} [DecidableEq Var] {Q w : ℕ} (O : Unitary (2 ^ w))
  (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w)
  (Δ : CQState (Store Var) (2 ^ Q)) (Θ : CQAssertion (Store Var) (2 ^ Q))

theorem unroll_expect_mono :
    Monotone fun M ↦ 𝔼[(interp ((unroll M c).compile O)).toStateFun Δ ⊨ Θ] := by
  intro m n hmn
  simp only [← expect_wp]
  exact expect_mono le_rfl ((convP O c Θ).1 hmn)

theorem unroll_expect_tendsto :
    Filter.Tendsto (fun M ↦ 𝔼[(interp ((unroll M c).compile O)).toStateFun Δ ⊨ Θ])
      Filter.atTop (nhds 𝔼[(interp (c.compile QProg.qAssign O)).toStateFun Δ ⊨ Θ]) := by
  simp only [← expect_wp]
  exact (convP O c Θ).2 Δ

end main

/-! ### Goal 3: states and costs -/

section cost

variable {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]

/-- The sublanguage with neither `assign` nor `qSet` (all that `compile` produces). -/
def Good : QProg Var d → Prop
  | .skip => True
  | .abort => True
  | .assign _ _ => False
  | .qMeasure _ _ => True
  | .qSet => False
  | .qAssign _ => True
  | .qSeq c₁ c₂ => Good c₁ ∧ Good c₂
  | @QProg.qIf _ _ _ _ c₁ c₂ => Good c₁ ∧ Good c₂
  | @QProg.qWhile _ _ _ _ c => Good c

/-- The state transformer of `S` is monotone. -/
def SMono (S : Q (Store Var) d Unit) : Prop :=
  ∀ Δ Δ' : CQState (Store Var) d, Δ ≤ Δ' → S.toStateFun Δ ≤ S.toStateFun Δ'

lemma cq_map_mono {State State' : Type} (f : State → State') {Δ Δ' : CQState State d}
    (h : Δ ≤ Δ') : Δ.map f ≤ Δ'.map f := fun σ' => by
  show ∑' σ : {σ // f σ = σ'}, (Δ σ.1).1 ≤ ∑' σ : {σ // f σ = σ'}, (Δ' σ.1).1
  exact (Δ.summable.subtype _).tsum_le_tsum (fun σ => h σ.1) (Δ'.summable.subtype _)

lemma smono_pure : SMono (pure () : Q (Store Var) d Unit) := fun _ _ h => h

lemma smono_bind {S T : Q (Store Var) d Unit} (hS : SMono S) (hT : SMono T) :
    SMono (S >>= fun _ => T) := fun Δ Δ' h => by
  simp only [Q.toStateFun_bind]
  exact hT _ _ (hS _ _ h)

lemma smono_cqIf (b : Store Var → Prop) [DecidablePred b] {S T : Q (Store Var) d Unit}
    (hS : SMono S) (hT : SMono T) : SMono (cqIf b S T) := fun Δ Δ' h => by
  simp only [Q.toStateFun_cqIf]
  exact CQState.add_mono (hS _ _ (CQState.restrict_mono _ h)) (hT _ _ (CQState.restrict_mono _ h))

lemma smono_whileRec (b : Store Var → Prop) [DecidablePred b] {S : Q (Store Var) d Unit}
    (hS : SMono S) (n : ℕ) : SMono (whileRec S b n) := by
  induction n with
  | zero => exact fun Δ Δ' _ => le_rfl
  | succ n ih =>
    rw [whileRec_succ]
    exact smono_cqIf b (smono_bind hS ih) smono_pure

lemma interp_mono {P : QProg Var d} (hP : Good P) : SMono (interp P) := by
  induction P with
  | skip => exact smono_pure
  | abort => exact fun Δ Δ' _ => le_rfl
  | assign x e => exact hP.elim
  | qMeasure x ℳ =>
    intro Δ Δ' h
    show CQState.qMeasurement x ℳ Δ ≤ CQState.qMeasurement x ℳ Δ'
    exact CQState.sum_mono (fun o => cq_map_mono _ (CQState.conj_mono h))
  | qSet => exact hP.elim
  | qAssign U =>
    intro Δ Δ' h
    show CQState.qAssign U Δ ≤ CQState.qAssign U Δ'
    exact CQState.conj_mono h
  | qSeq c₁ c₂ ih₁ ih₂ => exact smono_bind (ih₁ hP.1) (ih₂ hP.2)
  | qIf b c₁ c₂ ih₁ ih₂ => exact smono_cqIf b (ih₁ hP.1) (ih₂ hP.2)
  | qWhile b c ih =>
    intro Δ Δ' h
    have hn := smono_whileRec b (ih hP)
    refine OmegaCompletePartialOrder.ωSup_le _ _ fun n => ?_
    exact (hn n Δ Δ' h).trans
      (OmegaCompletePartialOrder.le_ωSup
        ((⟨whileRec (interp c) b, whileRec_monotone (interp c) b⟩ :
          OmegaCompletePartialOrder.Chain (Q (Store Var) d Unit)).map
            Q.toStateFunEmb.toOrderHom |>.map (Pi.evalOrderHom Δ')) n)

lemma whileRecCost_mono (b : Store Var → Prop) [DecidablePred b]
    {c : CQState (Store Var) d → ℝ≥0∞} {s : CQState (Store Var) d → CQState (Store Var) d}
    (hc : ∀ Δ Δ', Δ ≤ Δ' → c Δ ≤ c Δ') (hs : ∀ Δ Δ', Δ ≤ Δ' → s Δ ≤ s Δ') (n : ℕ) :
    ∀ Δ Δ' : CQState (Store Var) d, Δ ≤ Δ' → whileRecCost c s b n Δ ≤ whileRecCost c s b n Δ' := by
  induction n with
  | zero => intro Δ Δ' _; simp
  | succ n ih =>
    intro Δ Δ' h
    rw [whileRecCost_succ, whileRecCost_succ]
    exact add_le_add (hc _ _ (CQState.restrict_mono _ h)) (ih _ _ (hs _ _ (CQState.restrict_mono _ h)))

lemma whileRecCost_le (b : Store Var → Prop) [DecidablePred b]
    {cB cF : CQState (Store Var) d → ℝ≥0∞} {sB sF : CQState (Store Var) d → CQState (Store Var) d}
    (hcF : ∀ Δ Δ', Δ ≤ Δ' → cF Δ ≤ cF Δ') (hsF : ∀ Δ Δ', Δ ≤ Δ' → sF Δ ≤ sF Δ')
    (hc : ∀ Δ, cB Δ ≤ cF Δ) (hs : ∀ Δ, sB Δ ≤ sF Δ) (n : ℕ) :
    ∀ Δ : CQState (Store Var) d, whileRecCost cB sB b n Δ ≤ whileRecCost cF sF b n Δ := by
  induction n with
  | zero => intro Δ; simp
  | succ n ih =>
    intro Δ
    rw [whileRecCost_succ, whileRecCost_succ]
    exact add_le_add (hc _)
      ((ih _).trans (whileRecCost_mono b hcF hsF n _ _ (hs _)))

lemma cost_mono (model : CostModel d) {P : QProg Var d} (hP : Good P) :
    ∀ Δ Δ' : CQState (Store Var) d, Δ ≤ Δ' → expectedCost model P Δ ≤ expectedCost model P Δ' := by
  induction P with
  | skip => intro Δ Δ' _; exact le_rfl
  | abort => intro Δ Δ' _; exact le_rfl
  | assign x e => exact hP.elim
  | qMeasure x ℳ =>
    intro Δ Δ' h
    simp only [expectedCost_qMeasure]
    gcongr
  | qSet => exact hP.elim
  | qAssign U =>
    intro Δ Δ' h
    simp only [expectedCost_qAssign]
    gcongr
  | qSeq c₁ c₂ ih₁ ih₂ =>
    intro Δ Δ' h
    simp only [expectedCost_qSeq]
    exact add_le_add (ih₁ hP.1 _ _ h) (ih₂ hP.2 _ _ (interp_mono hP.1 _ _ h))
  | qIf b c₁ c₂ ih₁ ih₂ =>
    intro Δ Δ' h
    simp only [expectedCost_qIf]
    exact add_le_add (ih₁ hP.1 _ _ (CQState.restrict_mono _ h))
      (ih₂ hP.2 _ _ (CQState.restrict_mono _ h))
  | qWhile b c ih =>
    intro Δ Δ' h
    simp only [expectedCost_qWhile]
    exact iSup_mono fun n =>
      whileRecCost_mono b (ih hP) (interp_mono (P := c) hP) n _ _ h

lemma whileRec_state_le (b : Store Var → Prop) [DecidablePred b] {S T : Q (Store Var) d Unit}
    (hT : SMono T) (hST : ∀ Δ, S.toStateFun Δ ≤ T.toStateFun Δ) (n : ℕ) :
    ∀ Δ : CQState (Store Var) d, (whileRec S b n).toStateFun Δ ≤ (whileRec T b n).toStateFun Δ := by
  induction n with
  | zero => intro Δ; exact le_rfl
  | succ n ih =>
    intro Δ
    rw [whileRec_succ, whileRec_succ, Q.toStateFun_cqIf, Q.toStateFun_cqIf]
    refine CQState.add_mono ?_ le_rfl
    simp only [Q.toStateFun_bind]
    exact (ih _).trans (smono_whileRec b hT n _ _ (hST _))

end cost

/-! ### Compiled programs are `Good`, and unrolled loops -/

section compile2

variable {Var : Type} [DecidableEq Var] {Q w : ℕ}

lemma good_compile_lf (O : Unitary (2 ^ w)) (p : LF Var Q w) : Good (p.compile O) := by
  induction p with
  | skip => trivial
  | abort => trivial
  | step U => trivial
  | oracle r => trivial
  | measure v r => trivial
  | qIf b t f iht ihf => exact ⟨iht, ihf⟩
  | seq p₁ p₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩

lemma good_compile (O : Unitary (2 ^ w))
    (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w) :
    Good (c.compile QProg.qAssign O) := by
  induction c with
  | skip => trivial
  | step U => trivial
  | oracle r => trivial
  | measure v r => trivial
  | qIf b t f iht ihf => exact ⟨iht, ihf⟩
  | qWhile b body ih => exact ih
  | seq p₁ p₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩

lemma interp_compile_whileN (O : Unitary (2 ^ w)) (b : Store Var → Prop) [DecidablePred b]
    (B : LF Var Q w) (n : ℕ) :
    interp ((LF.whileN b B n).compile O) = whileRec (interp (B.compile O)) b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [LF.whileN, LF.compile, interp_qIf, interp_qSeq, interp_skip, whileRec_succ, ih]

lemma expectedCost_compile_whileN (model : CostModel (2 ^ Q)) (O : Unitary (2 ^ w))
    (b : Store Var → Prop) [DecidablePred b] (B : LF Var Q w) (n : ℕ) :
    ∀ Δ : CQState (Store Var) (2 ^ Q),
      expectedCost model ((LF.whileN b B n).compile O) Δ =
        whileRecCost (expectedCost model (B.compile O)) (interp (B.compile O)).toStateFun b n Δ := by
  induction n with
  | zero => intro Δ; rfl
  | succ n ih =>
    intro Δ
    simp only [LF.whileN, LF.compile, expectedCost_qIf, expectedCost_qSeq, expectedCost_skip,
      add_zero, whileRecCost_succ, ih]

/-- Domination of the state and of every expected cost by the library's semantics of the loop. -/
theorem approx_le (O : Unitary (2 ^ w)) (M : ℕ)
    (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w) :
    ∀ Δ : CQState (Store Var) (2 ^ Q),
      (interp ((unroll M c).compile O)).toStateFun Δ ≤
          (interp (c.compile QProg.qAssign O)).toStateFun Δ ∧
        ∀ model : CostModel (2 ^ Q), expectedCost model ((unroll M c).compile O) Δ ≤
          expectedCost model (c.compile QProg.qAssign O) Δ := by
  induction c with
  | skip => intro Δ; exact ⟨le_rfl, fun _ => le_rfl⟩
  | step U => intro Δ; exact ⟨le_rfl, fun _ => le_rfl⟩
  | oracle r => intro Δ; exact ⟨le_rfl, fun _ => le_rfl⟩
  | measure v r => intro Δ; exact ⟨le_rfl, fun _ => le_rfl⟩
  | qIf b t f iht ihf =>
    intro Δ
    simp only [unroll, LF.compile, OracleDynamicCircuit.compile_qIf, interp_qIf,
      QMonad.Q.toStateFun_cqIf, expectedCost_qIf]
    exact ⟨CQState.add_mono (iht _).1 (ihf _).1,
      fun model => add_le_add ((iht _).2 model) ((ihf _).2 model)⟩
  | qWhile b body ih =>
    intro Δ
    have hF := good_compile O body
    have hsem : ∀ Δ', (interp ((unroll M body).compile O)).toStateFun Δ' ≤
        (interp (body.compile QProg.qAssign O)).toStateFun Δ' := fun Δ' => (ih Δ').1
    refine ⟨?_, fun model => ?_⟩
    · simp only [unroll, OracleDynamicCircuit.compile_qWhile, interp_compile_whileN]
      refine (whileRec_state_le b (interp_mono hF) hsem M Δ).trans ?_
      exact (OmegaCompletePartialOrder.le_ωSup (α := QMonad.Q (Store Var) (2 ^ Q) Unit)
        ⟨whileRec (interp (body.compile QProg.qAssign O)) b,
          whileRec_monotone _ b⟩ M) Δ
    · simp only [unroll, OracleDynamicCircuit.compile_qWhile, expectedCost_compile_whileN,
        expectedCost_qWhile]
      refine (whileRecCost_le b (cost_mono model hF) (interp_mono hF) (fun Δ' => (ih Δ').2 model)
        hsem M Δ).trans ?_
      exact le_iSup (fun n => whileRecCost (expectedCost model (body.compile QProg.qAssign O))
        (interp (body.compile QProg.qAssign O)).toStateFun b n Δ) M
  | seq p₁ p₂ ih₁ ih₂ =>
    intro Δ
    simp only [unroll, LF.compile, OracleDynamicCircuit.compile_seq, interp_qSeq,
      QMonad.Q.toStateFun_bind, expectedCost_qSeq]
    have hA₂ := good_compile_lf O (unroll M p₂)
    refine ⟨((interp_mono hA₂) _ _ (ih₁ Δ).1).trans (ih₂ _).1, fun model => ?_⟩
    exact add_le_add ((ih₁ Δ).2 model)
      (((cost_mono model hA₂) _ _ (ih₁ Δ).1).trans ((ih₂ _).2 model))

end compile2

section main3

variable {Var : Type} [DecidableEq Var] {Q w : ℕ} (O : Unitary (2 ^ w))
  (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w)
  (Δ : CQState (Store Var) (2 ^ Q))

theorem unroll_cost_le (model : CostModel (2 ^ Q)) (M : ℕ) :
    expectedCost model ((unroll M c).compile O) Δ ≤
      expectedCost model (c.compile QProg.qAssign O) Δ :=
  (approx_le O M c Δ).2 model

end main3

#print axioms unroll_expect_mono
#print axioms unroll_expect_tendsto
#print axioms unroll_cost_le

end GroverLowerBound
