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
import LowerBounds.Grover.Statement
import LowerBounds.Grover.Defs
import LowerBounds.Grover.Link
import LowerBounds.Grover.Hybrid
import LowerBounds.Grover.Unroll
import Mathlib

/-!
# The find-any lower bound with constant 1/8

`GroverLowerBound.findAny_lower_bound : FindAnyLowerBound (1 / 8) 5`.

* `arith`: the real inequality `N ≤ (2T+1)^2 + N B / (T+1)` for all `T` forces `√N / 8 ≤ B`.
* list lemmas: Markov and the split of the success weight by `count ≤ T`.
* `cw_le`, `succ_le`: per marked item `x` and unrolling depth `M`.
* `findAny_lower_bound`: sum over `x`, let `M → ∞`, apply `arith`.
-/

open QuantumComputation.Specs Operator ResourceCounting Filter
open scoped Matrix QHLExpectation ComplexOrder MatrixOrder ENNReal NNReal
open QuantumComputation.Specs.Grover (Var)
open QuantumComputation.Specs.Grover.Var (res)

namespace GroverLowerBound

/-! ### Arithmetic -/

lemma arith (N B : ℝ) (hN : 32 ≤ N) (hB : 0 ≤ B)
    (h : ∀ T : ℕ, N ≤ (2 * (T : ℝ) + 1) ^ 2 + N * B / (T + 1)) : Real.sqrt N / 8 ≤ B := by
  by_contra hlt
  rw [not_le] at hlt
  have hNpos : 0 < N := by linarith
  have hs2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNpos.le
  have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hs : (28 / 5 : ℝ) ≤ Real.sqrt N := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    linarith
  set s := Real.sqrt N with hsdef
  have hT1 : ((⌊2 * B⌋₊ : ℕ) : ℝ) ≤ 2 * B := Nat.floor_le (by positivity)
  have hT2 : 2 * B < ((⌊2 * B⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  set T := ⌊2 * B⌋₊ with hT
  have h0 := h T
  have hpos : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have h3 : N * B / ((T : ℝ) + 1) < N / 2 := by
    rw [div_lt_iff₀ hpos]
    have := mul_lt_mul_of_pos_left hT2 hNpos
    nlinarith
  have h4 : (2 * (T : ℝ) + 1) ^ 2 ≤ (s / 2 + 1) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  nlinarith

/-! ### Lists -/

section lists

variable {α : Type}

/-- Split the weight of the good branches by `count ≤ T`. -/
lemma split_le (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (live g cnt : α → Bool) (L : List α) :
    ((L.filter fun a ↦ live a && g a).map f).sum ≤
      ((L.filter fun a ↦ live a && cnt a && g a).map f).sum +
        ((L.filter fun a ↦ live a && !cnt a).map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have := hf a
    simp only [List.filter_cons]
    cases live a <;> cases g a <;> cases cnt a <;> simp <;> linarith

end lists

section markov

variable {ι : Type} {Q : ℕ}

lemma markov (i : ι) (T : ℕ) (L : List (Branch Var ι Q)) :
    ((T : ℝ) + 1) * ((L.filter fun β ↦ β.live && !decide (β.count ≤ T)).map
      fun β ↦ nsq (β.vec i)).sum ≤ cw i L := by
  rw [cw_eq]
  induction L with
  | nil => simp
  | cons β L ih =>
    have h1 := nsq_nonneg (β.vec i)
    have h2 := cwt_nonneg i β
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    by_cases hl : β.live = true
    · by_cases hc : β.count ≤ T
      · simp [hl, hc, cwt]
        nlinarith
      · have hc' : (T : ℝ) + 1 ≤ β.count := by
          have : T + 1 ≤ β.count := by omega
          exact_mod_cast this
        simp [hl, hc, cwt]
        nlinarith
    · simp [hl, cwt]
      linarith

end markov

/-! ### One marked item -/

section item

variable {n Q : ℕ}

lemma hG_real (x : Fin (2 ^ n)) (k : ℕ) (r : QRegister ((n + 1) * 1) Q) :
    hybridG (some (x, 0)) k r = (r.embedUnitary (groverParallelMarkingOracle 1 {x})).1 := by
  simp [hybridG]

/-- The oracle-count weight of the real run on the unrolled program is at most the cost bound. -/
lemma cw_le (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1)) (σ₀ : Store Var)
    (x : Fin (2 ^ n)) (Δ₀ : CQState (Store Var) (2 ^ Q)) (htr : Δ₀.trace = 1)
    (hrep : Rep (CQState.qSet Δ₀) [(initBranch σ₀ : Branch Var (HIdx n) Q)] (some (x, 0)))
    (qx : ℝ≥0)
    (hq : CostBound (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle 1 {x}))
      (findAnyProgramOf c {x}) qx) (M : ℕ) :
    cw (some (x, 0)) (ens hybridG (unroll M c) [(initBranch σ₀ : Branch Var (HIdx n) Q)])
      ≤ (qx : ℝ) := by
  have h1 := rep_cost (i₀ := some (x, 0)) (groverParallelMarkingOracle 1 {x}) hybridG
    (hG_real x) (unroll M c) hrep
  have h0 : cw (some (x, 0)) [(initBranch σ₀ : Branch Var (HIdx n) Q)] = 0 := by
    simp [cw, initBranch]
  rw [h0, sub_zero] at h1
  have h2 := unroll_cost_le (groverParallelMarkingOracle 1 {x}) c (CQState.qSet Δ₀)
    (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle 1 {x})) M
  have h3 := hq Δ₀
  have h4 : expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle 1 {x}))
      (findAnyProgramOf c {x}) Δ₀ =
      expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle 1 {x}))
        (c.compile QProg.qAssign (groverParallelMarkingOracle 1 {x})) (CQState.qSet Δ₀) := by
    simp [findAnyProgramOf]
  rw [h4, htr] at h3
  have h5 := h1.trans (h2.trans h3)
  simp only [ENNReal.coe_one, one_mul] at h5
  have := (ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top).1 h5
  simpa using this

/-- The branches of the unrolled run. -/
noncomputable def htm (x : Fin (2 ^ n)) (T : ℕ) (E : List (Branch Var (HIdx n) Q)) : ℝ :=
  ((E.filter fun β ↦ β.live && decide (β.count ≤ T) && decide (β.store res = (x.val : ℤ))).map
    fun β ↦ nsq (β.vec (some (x, 0)))).sum

/-- The marked-item postcondition. -/
noncomputable def post (n Q : ℕ) (x : Fin (2 ^ n)) : CQAssertion (Store Var) (2 ^ Q) :=
  fun σ ↦ ⌜∃ y ∈ ({x} : Finset (Fin (2 ^ n))), σ res = y.val⌝

lemma post_eq (x : Fin (2 ^ n)) :
    post n Q x = fun σ ↦ ⌜σ res = (x.val : ℤ)⌝ := by
  funext σ
  simp [post]

/-- Success of the unrolled program is at most the hybrid term plus the Markov tail. -/
lemma succ_le (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1)) (σ₀ : Store Var)
    (x : Fin (2 ^ n)) (Δ₀ : CQState (Store Var) (2 ^ Q)) (htr : Δ₀.trace = 1)
    (hrep : Rep (CQState.qSet Δ₀) [(initBranch σ₀ : Branch Var (HIdx n) Q)] (some (x, 0)))
    (qx : ℝ≥0)
    (hq : CostBound (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle 1 {x}))
      (findAnyProgramOf c {x}) qx) (M T : ℕ) :
    𝔼[(interp ((unroll M c).compile (groverParallelMarkingOracle 1 {x}))).toStateFun
        (CQState.qSet Δ₀) ⊨ post n Q x] ≤
      htm x T (ens hybridG (unroll M c) [(initBranch σ₀ : Branch Var (HIdx n) Q)]) +
        (qx : ℝ) / ((T : ℝ) + 1) := by
  have hR := rep_interp (i₀ := some (x, 0)) (groverParallelMarkingOracle 1 {x}) hybridG
    (hG_real x) (unroll M c) hrep
  rw [post_eq, rep_post (fun σ : Store Var ↦ σ res = (x.val : ℤ)) hR]
  set E := ens hybridG (unroll M c) [(initBranch σ₀ : Branch Var (HIdx n) Q)] with hE
  have hs := split_le (fun β : Branch Var (HIdx n) Q ↦ nsq (β.vec (some (x, 0))))
    (fun β ↦ nsq_nonneg _) (fun β ↦ β.live) (fun β ↦ decide (β.store res = (x.val : ℤ)))
    (fun β ↦ decide (β.count ≤ T)) E
  have hm := markov (some (x, 0)) T E
  have hc := cw_le c σ₀ x Δ₀ htr hrep qx hq M
  have hpos : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have hw : ((E.filter fun β ↦ β.live && !decide (β.count ≤ T)).map
      fun β ↦ nsq (β.vec (some (x, 0)))).sum ≤ (qx : ℝ) / ((T : ℝ) + 1) := by
    rw [le_div_iff₀ hpos]
    linarith
  unfold htm
  linarith

end item

/-! ### The spec at one marked item -/

section spec

variable {n Q : ℕ}

lemma expect_findAny (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1))
    (S : Finset (Fin (2 ^ n))) (Δ : CQState (Store Var) (2 ^ Q))
    (Ψ : CQAssertion (Store Var) (2 ^ Q)) :
    𝔼[(interp (findAnyProgramOf c S)).toStateFun Δ ⊨ Ψ] =
      𝔼[(interp (c.compile QProg.qAssign (groverParallelMarkingOracle 1 S))).toStateFun
        (CQState.qSet Δ) ⊨ Ψ] := by
  rw [← expect_wp, ← expect_wp]
  simp only [findAnyProgramOf, wp_qSeq, wp_qSet]
  exact expect_qSet _ _

end spec

/-! ### The theorem -/

theorem findAny_lower_bound : FindAnyLowerBound (1 / 8) 5 := by
  classical
  intro n hn Q c hmeets bound hbound
  obtain ⟨q, hq, havg⟩ := hbound
  have hcard : (groverTargetSets n 1).card = 2 ^ n := by
    simp [groverTargetSets, Finset.card_powersetCard]
  have hsum : ∑ S ∈ groverTargetSets n 1, (q S : ℝ) = ∑ x : Fin (2 ^ n), (q {x} : ℝ) := by
    simp [groverTargetSets, Finset.powersetCard_one, Finset.sum_map]
  have hmem : ∀ x : Fin (2 ^ n), ({x} : Finset (Fin (2 ^ n))) ∈ groverTargetSets n 1 := by
    intro x
    simp [groverTargetSets, Finset.mem_powersetCard]
  have hB0 : 0 ≤ bound := le_trans (by positivity) havg
  have hsumle : ∑ x : Fin (2 ^ n), (q {x} : ℝ) ≤ 2 ^ n * bound := by
    rw [hsum, hcard] at havg
    have hp : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ) := by positivity
    rw [div_le_iff₀ hp] at havg
    push_cast at havg
    linarith
  have key : ∀ T : ℕ, (2 : ℝ) ^ n ≤ (2 * (T : ℝ) + 1) ^ 2 + (2 ^ n * bound) / ((T : ℝ) + 1) := by
    intro T
    let σ₀ : Store Var := fun _ ↦ 0
    choose Δ₀ htr hrep using
      fun x : Fin (2 ^ n) ↦ exists_init (ι := HIdx n) (Q := Q) (i₀ := some (x, 0)) σ₀
    let s : ℕ → Fin (2 ^ n) → ℝ := fun M x ↦
      𝔼[(interp ((unroll M c).compile (groverParallelMarkingOracle 1 {x}))).toStateFun
        (CQState.qSet (Δ₀ x)) ⊨ post n Q x]
    let L : Fin (2 ^ n) → ℝ := fun x ↦
      𝔼[(interp (c.compile QProg.qAssign (groverParallelMarkingOracle 1 {x}))).toStateFun
        (CQState.qSet (Δ₀ x)) ⊨ post n Q x]
    have hpos : (0 : ℝ) < (T : ℝ) + 1 := by positivity
    have hbd : ∀ M : ℕ, ∑ x, s M x ≤ (2 * (T : ℝ) + 1) ^ 2 + (2 ^ n * bound) / ((T : ℝ) + 1) := by
      intro M
      have h1 : ∀ x, s M x ≤ htm x T (ens hybridG (unroll M c)
          [(initBranch σ₀ : Branch Var (HIdx n) Q)]) + (q {x} : ℝ) / ((T : ℝ) + 1) :=
        fun x ↦ succ_le c σ₀ x (Δ₀ x) (htr x) (hrep x) (q {x}) (hq {x} (hmem x)) M T
      refine (Finset.sum_le_sum fun x _ ↦ h1 x).trans ?_
      rw [Finset.sum_add_distrib, ← Finset.sum_div]
      have h2 := hybrid_success_le res n Q T (unroll M c) σ₀
      have h3 : (∑ x, (q {x} : ℝ)) / ((T : ℝ) + 1) ≤ (2 ^ n * bound) / ((T : ℝ) + 1) :=
        div_le_div_of_nonneg_right hsumle hpos.le
      have h4 : ∑ x, htm x T (ens hybridG (unroll M c)
          [(initBranch σ₀ : Branch Var (HIdx n) Q)]) ≤ (2 * (T : ℝ) + 1) ^ 2 := h2
      linarith
    have hlim : Tendsto (fun M ↦ ∑ x, s M x) atTop (nhds (∑ x, L x)) := by
      refine tendsto_finsetSum _ fun x _ ↦ ?_
      exact unroll_expect_tendsto (groverParallelMarkingOracle 1 {x}) c (CQState.qSet (Δ₀ x))
        (post n Q x)
    have hL : ∀ x, 1 ≤ L x := by
      intro x
      have h : 𝔼[Δ₀ x ⊨ ⊤] ≤ L x := by
        have h0 := hmeets {x} (hmem x) (Δ₀ x)
        rw [expect_findAny] at h0
        exact h0
      rw [expect_top, htr x] at h
      exact_mod_cast h
    have hle : ∑ x, L x ≤ (2 * (T : ℝ) + 1) ^ 2 + (2 ^ n * bound) / ((T : ℝ) + 1) :=
      le_of_tendsto' hlim hbd
    have hge : (2 : ℝ) ^ n ≤ ∑ x, L x := by
      have := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) ↦ hL x
      simpa using this
    linarith
  have h32 : (32 : ℝ) ≤ (2 : ℝ) ^ n := by
    calc (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have := arith ((2 : ℝ) ^ n) bound h32 hB0 key
  linarith

end GroverLowerBound

#print axioms GroverLowerBound.findAny_lower_bound
