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
# Branch semantics against the library's semantics

The branch semantics `GroverLowerBound.ens` against the library's density-operator semantics,
through expectations only.

* `Rep Δ E i₀`: every expectation `𝔼[Δ ⊨ Θ]` is the sum of the quadratic forms of the live branches
  of `E` (run `i₀`).
* `rep_interp`, `rep_restrict`: `Rep` is preserved by `ens` / `interp` and by restriction.
* `rep_trace`, `rep_post`: trace and postcondition probabilities in terms of branch norms.
* `rep_cost`: the oracle-count weight `cw` increases by at most the library's expected oracle cost.
* `exists_init`: an initial cq-state represented by the initial branch.
-/

open QuantumComputation.Specs Operator ResourceCounting
open scoped Matrix QHLExpectation ComplexOrder MatrixOrder

namespace GroverLowerBound

/-! ### Quadratic forms -/

/-- The quadratic form `re ⟨v, A v⟩` of an observable. -/
noncomputable def qf {d : ℕ} (A : Observable (Fin d)) (v : Fin d → ℂ) : ℝ :=
  (star v ⬝ᵥ (A.1.mat *ᵥ v)).re

/-- The same quadratic form for a bare matrix. -/
noncomputable def qm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) : ℝ :=
  (star v ⬝ᵥ (M *ᵥ v)).re

lemma qf_eq_qm {d : ℕ} (A : Observable (Fin d)) (v : Fin d → ℂ) : qf A v = qm A.1.mat v := rfl

lemma qm_conj {d : ℕ} (M A : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) :
    qm (Mᴴ * A * M) v = qm A (M *ᵥ v) := by
  unfold qm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]

lemma qm_sum {d : ℕ} {α : Type*} (s : Finset α) (f : α → Matrix (Fin d) (Fin d) ℂ)
    (v : Fin d → ℂ) : qm (∑ a ∈ s, f a) v = ∑ a ∈ s, qm (f a) v := by
  unfold qm
  rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]

lemma qm_one {d : ℕ} (v : Fin d → ℂ) : qm 1 v = nsq v := by
  unfold qm nsq
  simp only [Matrix.one_mulVec, dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_apply, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

lemma qm_zero {d : ℕ} (v : Fin d → ℂ) : qm 0 v = 0 := by
  simp [qm]

lemma nsq_nonneg {d : ℕ} (v : Fin d → ℂ) : 0 ≤ nsq v :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

lemma qf_bot {d : ℕ} (v : Fin d → ℂ) : qf (⊥ : Observable (Fin d)) v = 0 := by
  have h : (⊥ : Observable (Fin d)).1.mat = 0 := rfl
  rw [qf_eq_qm, h, qm_zero]

lemma qf_top {d : ℕ} (v : Fin d → ℂ) : qf (⊤ : Observable (Fin d)) v = nsq v := by
  have h : (⊤ : Observable (Fin d)).1.mat = 1 := rfl
  rw [qf_eq_qm, h, qm_one]

lemma qf_conjUnitary {d : ℕ} (U : Unitary d) (A : Observable (Fin d)) (v : Fin d → ℂ) :
    qf (A.conjUnitary (star U)) v = qf A (U.1 *ᵥ v) := by
  have h : (A.conjUnitary (star U)).1.mat = U.1ᴴ * A.1.mat * U.1 :=
    CQAssertion.qAssign_apply_mat U (fun _ : Unit => A) ()
  rw [qf_eq_qm, h, qm_conj]
  rfl

lemma nsq_unitary {d : ℕ} (U : Unitary d) (v : Fin d → ℂ) : nsq (U.1 *ᵥ v) = nsq v := by
  have h : U.1ᴴ * (1 : Matrix (Fin d) (Fin d) ℂ) * U.1 = 1 := by
    rw [Matrix.mul_one]
    exact Unitary.star_mul_self_of_mem U.2
  rw [← qm_one, ← qm_conj, h]
  exact qm_one v

lemma qf_zero {d : ℕ} (v : Fin d → ℂ) : qf (0 : Observable (Fin d)) v = 0 := by
  have h : (0 : Observable (Fin d)).1.mat = 0 := rfl
  rw [qf_eq_qm, h, qm_zero]

lemma qf_one {d : ℕ} (v : Fin d → ℂ) : qf (1 : Observable (Fin d)) v = nsq v := by
  have h : (1 : Observable (Fin d)).1.mat = 1 := rfl
  rw [qf_eq_qm, h, qm_one]

lemma qf_qMeasure {Var : Type} [DecidableEq Var] {d i : ℕ} (ℳ : Measurement d i) (x : Var)
    (Θ : CQAssertion (Store Var) d) (σ : Store Var) (v : Fin d → ℂ) :
    qf (Θ.qMeasure ℳ x σ) v =
      ∑ o : Fin i, qf (Θ (Function.update σ x (o.1 : ℤ))) (ℳ.1 o *ᵥ v) := by
  have h : (Θ.qMeasure ℳ x σ).1.mat =
      ∑ o : Fin i, (ℳ.1 o)ᴴ * (Θ (Function.update σ x (o.1 : ℤ))).1.mat * ℳ.1 o := by
    simp [CQAssertion.qMeasure, CQAssertion.sum, HermitianMat.mat_finset_sum,
      HermitianMat.conj_apply_mat, Store.subst, CQAssertion.subst]
  rw [qf_eq_qm, h, qm_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [qm_conj]
  rfl

/-! ### Branch sums -/

section branches

variable {Var : Type} [DecidableEq Var] {ι : Type} {Q w : ℕ}

lemma filter_live_sum (g : Branch Var ι Q → ℝ) (E : List (Branch Var ι Q)) :
    ((E.filter (·.live)).map g).sum = (E.map fun β => if β.live then g β else 0).sum := by
  induction E with
  | nil => simp
  | cons β E ih =>
    by_cases h : β.live
    · simp [List.filter_cons, h, ih]
    · simp [List.filter_cons, h, ih]

lemma lsum_flatMap {α β : Type*} (g : α → List β) (f : β → ℝ) (l : List α) :
    ((l.flatMap g).map f).sum = (l.map fun a => ((g a).map f).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

lemma lsum_zero {α : Type*} (f : α → ℝ) (l : List α) (h : ∀ x ∈ l, f x = 0) :
    (l.map f).sum = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h a (by simp), ih fun x hx => h x (by simp [hx])]
    simp

/-- The weight of a branch under an assertion. -/
noncomputable def wt (i₀ : ι) (Θ : CQAssertion (Store Var) (2 ^ Q)) (β : Branch Var ι Q) : ℝ :=
  if β.live then qf (Θ β.store) (β.vec i₀) else 0

/-- The total weight of a branch list. -/
noncomputable def S (i₀ : ι) (Θ : CQAssertion (Store Var) (2 ^ Q))
    (E : List (Branch Var ι Q)) : ℝ :=
  (E.map (wt i₀ Θ)).sum

lemma S_append (i₀ : ι) (Θ : CQAssertion (Store Var) (2 ^ Q)) (E F : List (Branch Var ι Q)) :
    S i₀ Θ (E ++ F) = S i₀ Θ E + S i₀ Θ F := by
  simp [S]

lemma S_bot (i₀ : ι) (E : List (Branch Var ι Q)) :
    S i₀ (⊥ : CQAssertion (Store Var) (2 ^ Q)) E = 0 := by
  unfold S
  refine lsum_zero _ _ fun β _ => ?_
  simp [wt, qf_bot, qf_zero]

lemma S_top (i₀ : ι) (E : List (Branch Var ι Q)) :
    S i₀ (⊤ : CQAssertion (Store Var) (2 ^ Q)) E =
      ((E.filter (·.live)).map fun β => nsq (β.vec i₀)).sum := by
  rw [filter_live_sum]
  unfold S
  congr 1
  refine List.map_congr_left fun β _ => ?_
  simp [wt, qf_top, qf_one]

lemma S_ite (i₀ : ι) (b : Store Var → Prop) [DecidablePred b]
    (A B : CQAssertion (Store Var) (2 ^ Q)) (E : List (Branch Var ι Q)) :
    S i₀ (fun σ => if b σ then A σ else B σ) E =
      S i₀ A (E.filter fun β => decide (b β.store)) +
        S i₀ B (E.filter fun β => !decide (b β.store)) := by
  induction E with
  | nil => simp [S]
  | cons β E ih =>
    simp only [S, List.map_cons, List.sum_cons, List.filter_cons] at ih ⊢
    by_cases h : b β.store
    · have h1 : wt i₀ (fun σ => if b σ then A σ else B σ) β = wt i₀ A β := by simp [wt, h]
      simp [h, h1, ih]
      ring
    · have h1 : wt i₀ (fun σ => if b σ then A σ else B σ) β = wt i₀ B β := by simp [wt, h]
      simp [h, h1, ih]
      ring

/-! ### Representation -/

/-- `E` represents `Δ` at run `i₀`. -/
def Rep (Δ : CQState (Store Var) (2 ^ Q)) (E : List (Branch Var ι Q)) (i₀ : ι) : Prop :=
  ∀ Θ : CQAssertion (Store Var) (2 ^ Q),
    𝔼[Δ ⊨ Θ] = ((E.filter (·.live)).map fun β ↦ qf (Θ β.store) (β.vec i₀)).sum

lemma rep_iff {i₀ : ι} {Δ : CQState (Store Var) (2 ^ Q)} {E : List (Branch Var ι Q)} :
    Rep Δ E i₀ ↔ ∀ Θ : CQAssertion (Store Var) (2 ^ Q), 𝔼[Δ ⊨ Θ] = S i₀ Θ E := by
  unfold Rep S
  refine forall_congr' fun Θ => ?_
  rw [filter_live_sum]
  rfl

/-- The key identity: `ens` is dual to `wp`. -/
theorem S_wp {i₀ : ι} (O : Unitary (2 ^ w))
    (G : ι → ℕ → QRegister w Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (hG : ∀ k r, G i₀ k r = (r.embedUnitary O).1) :
    ∀ (P : LF Var Q w) (Θ : CQAssertion (Store Var) (2 ^ Q)) (E : List (Branch Var ι Q)),
      S i₀ (wp (P.compile O) Θ) E = S i₀ Θ (ens G P E) := by
  intro P
  induction P with
  | skip => intro Θ E; simp [LF.compile, ens]
  | abort =>
    intro Θ E
    simp only [LF.compile, wp, S_bot]
    symm
    unfold S
    refine lsum_zero _ _ fun β hβ => ?_
    simp only [ens, List.mem_map] at hβ
    obtain ⟨γ, _, rfl⟩ := hβ
    simp [wt]
  | step U =>
    intro Θ E
    simp only [LF.compile, wp, CQAssertion.qAssign, ens, S, List.map_map]
    congr 1
    refine List.map_congr_left fun β _ => ?_
    by_cases h : β.live
    · simp [wt, h]
      exact qf_conjUnitary U _ _
    · simp [wt, h]
  | oracle r =>
    intro Θ E
    simp only [LF.compile, wp, CQAssertion.qAssign, ens, S, List.map_map]
    congr 1
    refine List.map_congr_left fun β _ => ?_
    by_cases h : β.live
    · simp [wt, h, hG]
      exact qf_conjUnitary (r.embedUnitary O) _ _
    · simp [wt, h]
  | @measure k v r =>
    intro Θ E
    simp only [LF.compile, QProg.measureRegister, wp, ens, S, lsum_flatMap]
    congr 1
    refine List.map_congr_left fun β _ => ?_
    by_cases h : β.live
    · simp only [h, if_true, wt, qf_qMeasure, List.map_map]
      rw [Fin.sum_univ_def]
      congr 1
    · simp [wt, h]
  | qIf b t f iht ihf =>
    intro Θ E
    simp only [LF.compile, wp, ens]
    rw [S_ite, S_append, iht, ihf]
  | seq p₁ p₂ ih₁ ih₂ =>
    intro Θ E
    simp only [LF.compile, wp, ens]
    rw [ih₁, ih₂]

theorem rep_interp {i₀ : ι} {Δ : CQState (Store Var) (2 ^ Q)} {E : List (Branch Var ι Q)}
    (O : Unitary (2 ^ w)) (G : ι → ℕ → QRegister w Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (hG : ∀ k r, G i₀ k r = (r.embedUnitary O).1) (P : LF Var Q w) :
    Rep Δ E i₀ → Rep ((interp (P.compile O)).toStateFun Δ) (ens G P E) i₀ := by
  intro h
  rw [rep_iff] at h ⊢
  intro Θ
  rw [← expect_wp, h, S_wp O G hG]

theorem rep_restrict {i₀ : ι} {Δ : CQState (Store Var) (2 ^ Q)} {E : List (Branch Var ι Q)}
    (b : Store Var → Prop) [DecidablePred b] :
    Rep Δ E i₀ → Rep (Δ.restrict b) (E.filter fun β ↦ decide (b β.store)) i₀ := by
  intro h
  rw [rep_iff] at h ⊢
  intro Θ
  have h1 := h (fun σ => if b σ then Θ σ else (⊥ : CQAssertion (Store Var) (2 ^ Q)) σ)
  rw [expect_ite_partition, S_ite] at h1
  have h2 : 𝔼[Δ.restrict (¬ b ·) ⊨ (⊥ : CQAssertion (Store Var) (2 ^ Q))] = 0 := expect_bot _
  have h3 : S i₀ (⊥ : CQAssertion (Store Var) (2 ^ Q))
      (E.filter fun β => !decide (b β.store)) = 0 := S_bot _ _
  rw [h2, h3] at h1
  linarith

theorem rep_trace {i₀ : ι} {Δ : CQState (Store Var) (2 ^ Q)} {E : List (Branch Var ι Q)} :
    Rep Δ E i₀ → (Δ.trace : ℝ) = ((E.filter (·.live)).map fun β ↦ nsq (β.vec i₀)).sum := by
  intro h
  rw [rep_iff] at h
  rw [← S_top, ← h, expect_top]

theorem rep_post {i₀ : ι} {Δ : CQState (Store Var) (2 ^ Q)} {E : List (Branch Var ι Q)}
    (p : Store Var → Prop) [DecidablePred p] :
    Rep Δ E i₀ →
      𝔼[Δ ⊨ fun σ ↦ ⌜p σ⌝] =
        ((E.filter fun β ↦ β.live && decide (p β.store)).map fun β ↦ nsq (β.vec i₀)).sum := by
  intro h
  rw [expect_ofProp, rep_trace (rep_restrict p h), List.filter_filter]

/-! ### Cost -/

variable (i₀ : ι)

/-- The oracle-count weight: the number of oracle nodes passed times the squared norm. -/
noncomputable def cw (E : List (Branch Var ι Q)) : ℝ :=
  ((E.filter (·.live)).map fun β ↦ (β.count : ℝ) * nsq (β.vec i₀)).sum

/-- Branch-wise form of `cw`. -/
noncomputable def cwt (β : Branch Var ι Q) : ℝ :=
  if β.live then (β.count : ℝ) * nsq (β.vec i₀) else 0

lemma cw_eq (E : List (Branch Var ι Q)) : cw i₀ E = (E.map (cwt i₀)).sum := by
  unfold cw cwt
  exact filter_live_sum _ E

lemma cwt_nonneg (β : Branch Var ι Q) : 0 ≤ cwt i₀ β := by
  unfold cwt
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg _) (nsq_nonneg _)
  · exact le_rfl

lemma cw_nonneg (E : List (Branch Var ι Q)) : 0 ≤ cw i₀ E := by
  rw [cw_eq]
  induction E with
  | nil => simp
  | cons β E ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_nonneg (cwt_nonneg i₀ β) ih

lemma cw_append (E F : List (Branch Var ι Q)) : cw i₀ (E ++ F) = cw i₀ E + cw i₀ F := by
  simp [cw_eq]

lemma cw_split (b : Store Var → Prop) [DecidablePred b] (E : List (Branch Var ι Q)) :
    cw i₀ E = cw i₀ (E.filter fun β => decide (b β.store)) +
      cw i₀ (E.filter fun β => !decide (b β.store)) := by
  simp only [cw_eq]
  induction E with
  | nil => simp
  | cons β E ih =>
    by_cases h : b β.store
    · simp [List.filter_cons, h, ih]
      ring
    · simp [List.filter_cons, h, ih]
      ring

lemma cw_ens_dead (G : ι → ℕ → QRegister w Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (E : List (Branch Var ι Q)) : cw i₀ (ens G (.abort : LF Var Q w) E) = 0 := by
  rw [cw_eq]
  refine lsum_zero _ _ fun β hβ => ?_
  simp only [ens, List.mem_map] at hβ
  obtain ⟨γ, _, rfl⟩ := hβ
  simp [cwt]

lemma cw_ens_step (G : ι → ℕ → QRegister w Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (U : Unitary (2 ^ Q)) (E : List (Branch Var ι Q)) :
    cw i₀ (ens G (.step U : LF Var Q w) E) = cw i₀ E := by
  simp only [cw_eq, ens, List.map_map]
  congr 1
  refine List.map_congr_left fun β _ => ?_
  by_cases h : β.live
  · simp [cwt, h, nsq_unitary]
  · simp [cwt, h]

lemma cw_ens_oracle (O : Unitary (2 ^ w))
    (G : ι → ℕ → QRegister w Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (hG : ∀ k r, G i₀ k r = (r.embedUnitary O).1) (r : QRegister w Q)
    (E : List (Branch Var ι Q)) :
    cw i₀ (ens G (.oracle r : LF Var Q w) E) =
      cw i₀ E + ((E.filter (·.live)).map fun β ↦ nsq (β.vec i₀)).sum := by
  rw [filter_live_sum, cw_eq, cw_eq, ← List.sum_map_add]
  simp only [ens, List.map_map]
  congr 1
  refine List.map_congr_left fun β _ => ?_
  by_cases h : β.live
  · have hn : nsq (r.embedMatrix O.1 *ᵥ β.vec i₀) = nsq (β.vec i₀) :=
      nsq_unitary (r.embedUnitary O) _
    simp [cwt, h, hG, hn]
    ring
  · simp [cwt, h]

lemma cw_ens_measure {k : ℕ} (G : ι → ℕ → QRegister w Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (v : Var) (r : QRegister k Q) (E : List (Branch Var ι Q)) :
    cw i₀ (ens G (.measure v r : LF Var Q w) E) = cw i₀ E := by
  simp only [cw_eq, ens, lsum_flatMap]
  congr 1
  refine List.map_congr_left fun β _ => ?_
  by_cases h : β.live
  · rw [if_pos h, List.map_map]
    have key : ∀ o : Fin (2 ^ k),
        cwt i₀ ({ β with
          store := Function.update β.store v (o.val : ℤ)
          vec := fun i ↦ (r.computationalBasisMeasurement.1 o) *ᵥ β.vec i } : Branch Var ι Q) =
        (β.count : ℝ) * ∑ j : Fin (2 ^ Q),
          if r.extractIndex j = o then Complex.normSq (β.vec i₀ j) else 0 := by
      intro o
      simp only [cwt, h, if_true, nsq, QRegister.computationalBasisMeasurement_apply,
        QRegister.basisOutcomeProjector_mulVec]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    have : ((List.finRange (2 ^ k)).map fun o ↦ cwt i₀ ({ β with
          store := Function.update β.store v (o.val : ℤ)
          vec := fun i ↦ (r.computationalBasisMeasurement.1 o) *ᵥ β.vec i } : Branch Var ι Q))
        = (List.finRange (2 ^ k)).map fun o : Fin (2 ^ k) => (β.count : ℝ) * ∑ j : Fin (2 ^ Q),
          if r.extractIndex j = o then Complex.normSq (β.vec i₀ j) else 0 :=
      List.map_congr_left fun o _ => key o
    simp only [Function.comp_def]
    rw [this, ← Fin.sum_univ_def (fun o : Fin (2 ^ k) => (β.count : ℝ) * ∑ j : Fin (2 ^ Q),
          if r.extractIndex j = o then Complex.normSq (β.vec i₀ j) else 0), ← Finset.mul_sum,
      Finset.sum_comm]
    simp [cwt, h, nsq]
  · simp [cwt, h]

variable {i₀}

theorem rep_cost {Δ : CQState (Store Var) (2 ^ Q)} {E : List (Branch Var ι Q)}
    (O : Unitary (2 ^ w)) (G : ι → ℕ → QRegister w Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (hG : ∀ k r, G i₀ k r = (r.embedUnitary O).1) (P : LF Var Q w) :
    Rep Δ E i₀ →
      ENNReal.ofReal (cw i₀ (ens G P E) - cw i₀ E) ≤
        expectedCost (CostModel.ofEmbeddedOracle O) (P.compile O) Δ := by
  induction P generalizing Δ E with
  | skip => intro _; simp [ens]
  | abort =>
    intro _
    rw [cw_ens_dead]
    have := cw_nonneg i₀ E
    rw [ENNReal.ofReal_of_nonpos (by linarith)]
    exact bot_le
  | step U =>
    intro _
    rw [cw_ens_step]
    simp
  | oracle r =>
    intro h
    rw [cw_ens_oracle i₀ O G hG, add_sub_cancel_left, ← rep_trace h]
    simp [LF.compile, expectedCost]
  | measure v r =>
    intro _
    rw [cw_ens_measure]
    simp
  | qIf b t f iht ihf =>
    intro h
    simp only [LF.compile, expectedCost, ens]
    have hs := cw_split i₀ b E
    have h1 := iht (rep_restrict b h)
    have h2 : Rep (Δ.restrict (¬ b ·)) (E.filter fun β => !decide (b β.store)) i₀ := by
      have := rep_restrict (fun σ => ¬ b σ) h
      simpa [decide_not] using this
    have h3 := ihf h2
    rw [cw_append, hs]
    have e : ∀ a b c d : ℝ, a + b - (c + d) = (a - c) + (b - d) := fun a b c d => by ring
    rw [e]
    exact ENNReal.ofReal_add_le.trans (add_le_add h1 h3)
  | seq p₁ p₂ ih₁ ih₂ =>
    intro h
    simp only [LF.compile, expectedCost, ens]
    have h1 := ih₁ h
    have h2 := ih₂ (rep_interp O G hG p₁ h)
    calc ENNReal.ofReal (cw i₀ (ens G p₂ (ens G p₁ E)) - cw i₀ E)
        = ENNReal.ofReal ((cw i₀ (ens G p₂ (ens G p₁ E)) - cw i₀ (ens G p₁ E)) +
            (cw i₀ (ens G p₁ E) - cw i₀ E)) := by congr 1; ring
      _ ≤ ENNReal.ofReal (cw i₀ (ens G p₂ (ens G p₁ E)) - cw i₀ (ens G p₁ E)) +
            ENNReal.ofReal (cw i₀ (ens G p₁ E) - cw i₀ E) := ENNReal.ofReal_add_le
      _ ≤ _ := by
          rw [add_comm]
          exact add_le_add h1 h2

/-! ### Initial state -/

theorem exists_init {i₀ : ι} (σ₀ : Store Var) :
    ∃ Δ₀ : CQState (Store Var) (2 ^ Q), Δ₀.trace = 1 ∧
      Rep (CQState.qSet Δ₀) [(initBranch σ₀ : Branch Var ι Q)] i₀ := by
  classical
  let f : Store Var → 𝒟 (Fin (2 ^ Q)) :=
    fun σ => if σ = σ₀ then PartialDensityOperator.single 0 1 else 0
  have hs : HasSum (fun σ => (f σ).trace) 1 := by
    have := hasSum_ite_eq σ₀ (1 : NNReal)
    convert this using 1
    funext σ
    by_cases h : σ = σ₀
    · simp [f, h, PartialDensityOperator.trace_single]
    · simp [f, h]
  let Δ₀ : CQState (Store Var) (2 ^ Q) := ⟨f, 1, hs, le_rfl⟩
  refine ⟨Δ₀, hs.tsum_eq, ?_⟩
  intro Θ
  rw [← expect_qSet, expect_eq_tsum, tsum_eq_single σ₀]
  · have h0 : (Δ₀ σ₀).1 = HermitianMat.single (0 : Fin (2 ^ Q)) ((1 : unitInterval) : ℝ) := by
      simp [Δ₀, f, PartialDensityOperator.single]
    rw [h0, HermitianMat.inner_eq_re_trace, CQAssertion.qSet_apply_mat]
    simp [HermitianMat.single_mat, initBranch, qf]
  · intro σ hσ
    have : (Δ₀ σ).1 = 0 := by simp [Δ₀, f, hσ]
    rw [this]
    simp

end branches

end GroverLowerBound

#print axioms GroverLowerBound.rep_interp
#print axioms GroverLowerBound.rep_restrict
#print axioms GroverLowerBound.rep_trace
#print axioms GroverLowerBound.rep_post
#print axioms GroverLowerBound.rep_cost
#print axioms GroverLowerBound.exists_init
