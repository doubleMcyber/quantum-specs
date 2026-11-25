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
import LowerBounds.Grover.EighthBound
import LowerBounds.Grover.Unroll
import LowerBounds.Grover.Lines
import LowerBounds.Grover.Mean
import LowerBounds.Grover.Cost
import Mathlib

/-!
# The find-any lower bound with constant 3/5

`GroverThreeFifths.findAny_lower_bound_35 : GroverLowerBound.FindAnyLowerBound (3 / 5) 16`.

Assembly of the piecewise-linear potential `Vpl` (`Lines.lean`), the mean inequality
(`Mean.lean`) and the all-branch cost, mass and end bound (`Cost.lean`) in the template of
`GroverLowerBound.findAny_lower_bound` (`EighthBound.lean`). The run index is `Fin (2 ^ n)` and
run `x` applies the oracle of the marked item `x` at every oracle node. The branch weight is
`pw t β = t * Vpl (‖mean‖²) (avgW) + count * avgW`, which does not decrease along `ens`.
-/

open QuantumComputation.Specs Operator ResourceCounting Filter
open scoped Matrix QHLExpectation ComplexOrder MatrixOrder ENNReal NNReal
open QuantumComputation.Specs.Grover (Var)
open QuantumComputation.Specs.Grover.Var (res)

namespace GroverThreeFifths

open GroverLowerBound

/-- The oracle matrices: run `x` applies the oracle of the marked item `x`. -/
noncomputable def GM (n Q : ℕ) :
    Fin (2 ^ n) → ℕ → QRegister ((n + 1) * 1) Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ :=
  fun x _ r => (r.embedUnitary (groverParallelMarkingOracle 1 {x})).1

/-- The branch weight. -/
noncomputable def pw {n Q : ℕ} (t : ℝ) (β : Branch Var (Fin (2 ^ n)) Q) : ℝ :=
  t * Vpl (nsq (meanV β.vec)) (avgW β.vec) + (β.count : ℝ) * avgW β.vec

/-! ### Small facts -/

lemma Vpl_fin_sum {k : ℕ} (C W : Fin k → ℝ) :
    Vpl (∑ o, C o) (∑ o, W o) ≤ ∑ o, Vpl (C o) (W o) := by
  have := Vpl_list_sum (List.finRange k) C W
  simpa only [Fin.sum_univ_def] using this

lemma sum_nsq_meanV_measure {n Q k : ℕ} (r : QRegister k Q) (v : Fin (2 ^ n) → Fin (2 ^ Q) → ℂ) :
    ∑ o : Fin (2 ^ k), nsq (meanV (fun i => (r.computationalBasisMeasurement.1 o) *ᵥ v i)) =
      nsq (meanV v) := by
  simp only [meanV_mulVec]
  exact sum_nsq_measure r.computationalBasisMeasurement (meanV v)

lemma avgW_measure {n Q k : ℕ} (r : QRegister k Q) (v : Fin (2 ^ n) → Fin (2 ^ Q) → ℂ) :
    ∑ o : Fin (2 ^ k), avgW (fun i => (r.computationalBasisMeasurement.1 o) *ᵥ v i) =
      avgW v := by
  unfold avgW
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun x _ => sum_nsq_measure r.computationalBasisMeasurement (v x)

lemma avgW_nonneg' {n Q : ℕ} (v : Fin (2 ^ n) → Fin (2 ^ Q) → ℂ) : 0 ≤ avgW v :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => nsq_nonneg _)

lemma meanV_const {n Q : ℕ} (e : Fin (2 ^ Q) → ℂ) :
    meanV (fun _ : Fin (2 ^ n) => e) = e := by
  funext j
  simp only [meanV, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : ((2 ^ n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  exact inv_mul_cancel_left₀ this _

lemma avgW_const {n Q : ℕ} (e : Fin (2 ^ Q) → ℂ) :
    avgW (fun _ : Fin (2 ^ n) => e) = nsq e := by
  unfold avgW
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : ((2 ^ n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  exact inv_mul_cancel_left₀ this _

lemma list_lin {α : Type} (E : List α) (a m : α → ℝ) (c : ℝ) :
    (E.map fun β ↦ c * a β + m β).sum = c * (E.map a).sum + (E.map m).sum := by
  induction E with
  | nil => simp
  | cons b E ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

lemma list_mul {α : Type} (E : List α) (f : α → ℝ) (c : ℝ) :
    c * (E.map f).sum = (E.map fun a ↦ c * f a).sum := by
  induction E with
  | nil => simp
  | cons b E ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, ih]

/-! ### The weight does not decrease -/

theorem pw_ens_mono (n Q : ℕ) (t : ℝ) (ht : t = Real.sqrt (2 ^ n)) (ht256 : 256 ≤ t)
    (P : LF Var Q ((n + 1) * 1)) (E : List (Branch Var (Fin (2 ^ n)) Q)) :
    (E.map (pw t)).sum ≤ ((ens (GM n Q) P E).map (pw t)).sum := by
  have ht0 : 0 ≤ t := by linarith
  have h := ens_sum_mono (GM n Q) (fun _ : Branch Var (Fin (2 ^ n)) Q => True) (pw t)
    (fun _ _ _ _ _ => trivial)
    (fun β _ => le_of_eq (by simp [pw]))
    (fun U β _ => by
      by_cases h : β.live
      · rw [if_pos h]
        refine le_of_eq ?_
        simp only [pw, meanV_mulVec, nsq_unit, avgW_unitary]
      · rw [if_neg h])
    (fun r β _ => by
      by_cases h : β.live
      · rw [if_pos h]
        have hq : (1 - 2 / t ^ 2) * Real.sqrt (nsq (meanV β.vec))
            - 2 / t * Real.sqrt (avgW β.vec - nsq (meanV β.vec))
            ≤ Real.sqrt (nsq (meanV (fun i => GM n Q i β.count r *ᵥ β.vec i))) := by
          rw [ht]
          exact mean_query r β.vec
        have h1 := Vpl_query t (nsq (meanV β.vec)) (avgW β.vec)
          (nsq (meanV (fun i => GM n Q i β.count r *ᵥ β.vec i)))
          ht256 (nsq_nonneg _) (nsq_meanV_le _) (nsq_nonneg _) hq
        have h2 : avgW (fun i => GM n Q i β.count r *ᵥ β.vec i) = avgW β.vec :=
          avgW_oracle r β.vec
        simp only [pw]
        rw [h2]
        push_cast
        linarith
      · rw [if_neg h])
    (fun {k} v r β _ => by
      by_cases h : β.live
      · rw [if_pos h, sum_finRange_map]
        have hV := Vpl_fin_sum
          (fun o : Fin (2 ^ k) =>
            nsq (meanV (fun i => (r.computationalBasisMeasurement.1 o) *ᵥ β.vec i)))
          (fun o => avgW (fun i => (r.computationalBasisMeasurement.1 o) *ᵥ β.vec i))
        rw [sum_nsq_meanV_measure, avgW_measure] at hV
        have h2 := mul_le_mul_of_nonneg_left hV ht0
        simp only [pw, Finset.sum_add_distrib, ← Finset.mul_sum, avgW_measure]
        linarith
      · rw [if_neg h]
        simp)
    P E (fun _ _ => trivial)
  exact h

/-! ### One marked item -/

section item

variable {n Q : ℕ}

lemma hG_M (x : Fin (2 ^ n)) (k : ℕ) (r : QRegister ((n + 1) * 1) Q) :
    GM n Q x k r = (r.embedUnitary (groverParallelMarkingOracle 1 {x})).1 := rfl

/-- The oracle-count weight of the real run on the unrolled program is at most the cost bound. -/
lemma cwa_le (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1)) (σ₀ : Store Var)
    (x : Fin (2 ^ n)) (Δ₀ : CQState (Store Var) (2 ^ Q)) (htr : Δ₀.trace = 1)
    (hrep : Rep (CQState.qSet Δ₀) [(initBranch σ₀ : Branch Var (Fin (2 ^ n)) Q)] x)
    (qx : ℝ≥0)
    (hq : CostBound (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle 1 {x}))
      (findAnyProgramOf c {x}) qx) (M : ℕ) :
    cwa x (ens (GM n Q) (unroll M c) [(initBranch σ₀ : Branch Var (Fin (2 ^ n)) Q)])
      ≤ (qx : ℝ) := by
  have h1 := rep_cost_all (i₀ := x) (groverParallelMarkingOracle 1 {x}) (GM n Q) (hG_M x)
    (unroll M c) hrep
  have h0 : cwa x [(initBranch σ₀ : Branch Var (Fin (2 ^ n)) Q)] = 0 := by
    simp [cwa, initBranch]
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

/-- The success expectation of the unrolled program is the success weight of the branches. -/
lemma succ_eq (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1)) (σ₀ : Store Var)
    (x : Fin (2 ^ n)) (Δ₀ : CQState (Store Var) (2 ^ Q))
    (hrep : Rep (CQState.qSet Δ₀) [(initBranch σ₀ : Branch Var (Fin (2 ^ n)) Q)] x) (M : ℕ) :
    𝔼[(interp ((unroll M c).compile (groverParallelMarkingOracle 1 {x}))).toStateFun
        (CQState.qSet Δ₀) ⊨ post n Q x] =
      succ x (ens (GM n Q) (unroll M c) [(initBranch σ₀ : Branch Var (Fin (2 ^ n)) Q)]) := by
  have hR := rep_interp (i₀ := x) (groverParallelMarkingOracle 1 {x}) (GM n Q) (hG_M x)
    (unroll M c) hrep
  rw [post_eq, rep_post (fun σ : Store Var ↦ σ res = (x.val : ℤ)) hR]
  rfl

end item

/-! ### Sums over the branches of the unrolled run -/

section ends

variable {n Q : ℕ}

lemma start_pw (t : ℝ) (σ₀ : Store Var) :
    pw t (initBranch σ₀ : Branch Var (Fin (2 ^ n)) Q) = t * Vpl 1 1 := by
  have e : (initBranch σ₀ : Branch Var (Fin (2 ^ n)) Q).vec =
      fun _ => Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ) := rfl
  unfold pw
  rw [e, meanV_const, avgW_const, nsq_init]
  simp [initBranch]

lemma end_pw (t : ℝ) (ht : 0 ≤ t) (E : List (Branch Var (Fin (2 ^ n)) Q)) :
    (E.map (pw t)).sum ≤
      t * g1 * (E.map fun β ↦ nsq (meanV β.vec)).sum +
        (E.map fun β ↦ (β.count : ℝ) * avgW β.vec).sum := by
  have h : (E.map (pw t)).sum ≤
      (E.map fun β ↦ (t * g1) * nsq (meanV β.vec) + (β.count : ℝ) * avgW β.vec).sum := by
    refine List.sum_le_sum fun β _ => ?_
    unfold pw
    have := Vpl_le (nsq (meanV β.vec)) (avgW β.vec) (nsq_nonneg _) (nsq_meanV_le _)
    have := mul_le_mul_of_nonneg_left this ht
    linarith
  rw [list_lin] at h
  exact h

lemma cwa_sum (E : List (Branch Var (Fin (2 ^ n)) Q)) :
    ∑ x : Fin (2 ^ n), cwa x E =
      ((2 ^ n : ℕ) : ℝ) * (E.map fun β ↦ (β.count : ℝ) * avgW β.vec).sum := by
  unfold cwa
  rw [finset_sum_list_sum, list_mul]
  congr 1
  refine List.map_congr_left fun β _ => ?_
  have hN : ((2 ^ n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  rw [← Finset.mul_sum]
  unfold avgW
  field_simp

end ends

/-! ### The theorem -/

theorem findAny_lower_bound_35 : GroverLowerBound.FindAnyLowerBound (3 / 5) 16 := by
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
  have hsumle : ∑ x : Fin (2 ^ n), (q {x} : ℝ) ≤ 2 ^ n * bound := by
    rw [hsum, hcard] at havg
    have hp : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ) := by positivity
    rw [div_le_iff₀ hp] at havg
    push_cast at havg
    linarith
  -- numbers
  have hNpos : (0 : ℝ) < 2 ^ n := by positivity
  have hN16 : (2 : ℝ) ^ 16 ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have ht256 : (256 : ℝ) ≤ Real.sqrt (2 ^ n) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    norm_num at hN16
    linarith
  set t : ℝ := Real.sqrt (2 ^ n) with htdef
  have ht0 : 0 ≤ t := by linarith
  have hNnat : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
  let σ₀ : Store Var := fun _ ↦ 0
  choose Δ₀ htr hrep using
    fun x : Fin (2 ^ n) ↦ exists_init (ι := Fin (2 ^ n)) (Q := Q) (i₀ := x) σ₀
  let s : ℕ → Fin (2 ^ n) → ℝ := fun M x ↦
    𝔼[(interp ((unroll M c).compile (groverParallelMarkingOracle 1 {x}))).toStateFun
      (CQState.qSet (Δ₀ x)) ⊨ post n Q x]
  let L : Fin (2 ^ n) → ℝ := fun x ↦
    𝔼[(interp (c.compile QProg.qAssign (groverParallelMarkingOracle 1 {x}))).toStateFun
      (CQState.qSet (Δ₀ x)) ⊨ post n Q x]
  have hL : ∀ x, 1 ≤ L x := by
    intro x
    have h : 𝔼[Δ₀ x ⊨ ⊤] ≤ L x := by
      have h0 := hmeets {x} (hmem x) (Δ₀ x)
      rw [expect_findAny] at h0
      exact h0
    rw [expect_top, htr x] at h
    exact_mod_cast h
  let init : List (Branch Var (Fin (2 ^ n)) Q) := [initBranch σ₀]
  -- the inequality for every unrolling depth
  have hM : ∀ M : ℕ, t * g1 ≤ t * g1 * (2 / 2 ^ n + 2 / 2 ^ n * ∑ x, (1 - s M x)) + bound := by
    intro M
    set E := ens (GM n Q) (unroll M c) init with hE
    have h1 := pw_ens_mono n Q t htdef ht256 (unroll M c) init
    have h2 : t * g1 ≤ (init.map (pw t)).sum := by
      have : (init.map (pw t)).sum = t * Vpl 1 1 := by
        simp only [init, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        exact start_pw t σ₀
      rw [this]
      exact mul_le_mul_of_nonneg_left g1_le_Vpl_one ht0
    have h3 := end_pw t ht0 E
    have hmass : ∀ x, (E.map fun β ↦ nsq (β.vec x)).sum ≤ 1 := by
      intro x
      have h := mass_ens_le (GM n Q) (fun i k r v ↦ nsq_unitary _ v) (unroll M c) init x
      have h' : (init.map fun β ↦ nsq (β.vec x)).sum = 1 := by
        simp only [init, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        exact nsq_init Q
      linarith
    have h4 := sum_meanV_le E hmass
    have hs : ∀ x, s M x = succ x E := fun x ↦ succ_eq c σ₀ x (Δ₀ x) (hrep x) M
    have h5 : ∑ x, (1 - succ x E) = ∑ x, (1 - s M x) :=
      Finset.sum_congr rfl fun x _ ↦ by rw [hs x]
    rw [h5] at h4
    -- the cost term
    have h6 : ∑ x, cwa x E ≤ ∑ x : Fin (2 ^ n), (q {x} : ℝ) :=
      Finset.sum_le_sum fun x _ ↦
        cwa_le c σ₀ x (Δ₀ x) (htr x) (hrep x) (q {x}) (hq {x} (hmem x)) M
    have h7 := cwa_sum E
    have h8 : (E.map fun β ↦ (β.count : ℝ) * avgW β.vec).sum ≤ bound := by
      rw [hNnat] at h7
      have : (2 : ℝ) ^ n * (E.map fun β ↦ (β.count : ℝ) * avgW β.vec).sum ≤ 2 ^ n * bound := by
        rw [← h7]
        linarith
      exact le_of_mul_le_mul_left this hNpos
    have h9 : t * g1 * (E.map fun β ↦ nsq (meanV β.vec)).sum ≤
        t * g1 * (2 / 2 ^ n + 2 / 2 ^ n * ∑ x, (1 - s M x)) := by
      apply mul_le_mul_of_nonneg_left h4
      have : (0 : ℝ) ≤ g1 := by unfold g1; norm_num
      positivity
    linarith
  -- let the depth go to infinity
  have hlim : Tendsto (fun M ↦ ∑ x, (1 - s M x)) atTop (nhds (∑ x, (1 - L x))) := by
    refine tendsto_finsetSum _ fun x _ ↦ ?_
    exact tendsto_const_nhds.sub
      (unroll_expect_tendsto (groverParallelMarkingOracle 1 {x}) c (CQState.qSet (Δ₀ x))
        (post n Q x))
  have hg0 : (0 : ℝ) ≤ g1 := by unfold g1; norm_num
  set β : ℝ := t * g1 * (2 / 2 ^ n) with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hlim2 := hlim.const_mul β
  have hge : t * g1 - β - bound ≤ β * ∑ x, (1 - L x) := by
    refine ge_of_tendsto' hlim2 fun M ↦ ?_
    have := hM M
    have e : t * g1 * (2 / 2 ^ n + 2 / 2 ^ n * ∑ x, (1 - s M x)) =
        β + β * ∑ x, (1 - s M x) := by rw [hβ]; ring
    linarith
  have hneg : ∑ x, (1 - L x) ≤ 0 :=
    Finset.sum_nonpos fun x _ ↦ by linarith [hL x]
  have hz : β * ∑ x, (1 - L x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ0 hneg
  have hfin : t * (g1 * (1 - 2 / 2 ^ n)) ≤ bound := by
    have e : t * (g1 * (1 - 2 / 2 ^ n)) = t * g1 - β := by rw [hβ]; ring
    rw [e]
    linarith
  have hgb := mul_le_mul_of_nonneg_left (g1_bound (2 ^ n) hN16) ht0
  show 3 / 5 * t ≤ bound
  linarith

end GroverThreeFifths

#print axioms GroverThreeFifths.findAny_lower_bound_35
