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
import LowerBounds.Grover.FullStatement
import LowerBounds.Grover.FullQuery
import LowerBounds.Grover.ThreeFifthsBound
import Mathlib

/-!
# The find-any lower bound with constant π/8 + 1/4

`GroverThreeFifths.findAny_lower_bound_full : GroverThreeFifths.FullConstantTarget`, that is,
`(π / 8 + 1 / 4) * √(2 ^ n) - 4 / √(2 ^ n) ≤ bound` for every `n ≥ 2`.

The assembly is that of `findAny_lower_bound_35` (`ThreeFifthsBound.lean`), with the
piecewise-linear potential replaced by `Vf` (`FullPotential.lean`) and the oracle step by
`Vf_query` (`FullQuery.lean`). The branch weight is
`pwf κ β = κ * Vf (‖mean‖²) (avgW) + count * avgW` with `κ = 2 / arcsin (2 / t)`, `t = √(2 ^ n)`.
-/

open QuantumComputation.Specs Operator ResourceCounting Filter
open scoped Matrix QHLExpectation ComplexOrder MatrixOrder ENNReal NNReal
open QuantumComputation.Specs.Grover (Var)
open QuantumComputation.Specs.Grover.Var (res)

namespace GroverThreeFifths

open GroverLowerBound

/-- The branch weight for the full constant. -/
noncomputable def pwf {n Q : ℕ} (κ : ℝ) (β : Branch Var (Fin (2 ^ n)) Q) : ℝ :=
  κ * Vf (nsq (meanV β.vec)) (avgW β.vec) + (β.count : ℝ) * avgW β.vec

/-! ### The weight does not decrease -/

theorem pwf_ens_mono (n Q : ℕ) (t : ℝ) (ht : t = Real.sqrt (2 ^ n)) (ht2 : 2 ≤ t)
    (P : LF Var Q ((n + 1) * 1)) (E : List (Branch Var (Fin (2 ^ n)) Q)) :
    (E.map (pwf (2 / Real.arcsin (2 / t)))).sum ≤
      ((ens (GM n Q) P E).map (pwf (2 / Real.arcsin (2 / t)))).sum := by
  have hκ := kappa_pos t ht2
  have h := ens_sum_mono (GM n Q) (fun _ : Branch Var (Fin (2 ^ n)) Q => True)
    (pwf (2 / Real.arcsin (2 / t)))
    (fun _ _ _ _ _ => trivial)
    (fun β _ => le_of_eq (by simp [pwf]))
    (fun U β _ => by
      by_cases h : β.live
      · rw [if_pos h]
        refine le_of_eq ?_
        simp only [pwf, meanV_mulVec, nsq_unit, avgW_unitary]
      · rw [if_neg h])
    (fun r β _ => by
      by_cases h : β.live
      · rw [if_pos h]
        have hq : (1 - 2 / t ^ 2) * Real.sqrt (nsq (meanV β.vec))
            - 2 / t * Real.sqrt (avgW β.vec - nsq (meanV β.vec))
            ≤ Real.sqrt (nsq (meanV (fun i => GM n Q i β.count r *ᵥ β.vec i))) := by
          rw [ht]
          exact mean_query r β.vec
        have h2 : avgW (fun i => GM n Q i β.count r *ᵥ β.vec i) = avgW β.vec :=
          avgW_oracle r β.vec
        have h1 := Vf_query t (nsq (meanV β.vec)) (avgW β.vec)
          (nsq (meanV (fun i => GM n Q i β.count r *ᵥ β.vec i)))
          ht2 (nsq_nonneg _) (nsq_meanV_le _) (nsq_nonneg _)
          (h2 ▸ nsq_meanV_le (fun i => GM n Q i β.count r *ᵥ β.vec i)) hq
        simp only [pwf]
        rw [h2]
        push_cast
        linarith
      · rw [if_neg h])
    (fun {k} v r β _ => by
      by_cases h : β.live
      · rw [if_pos h, sum_finRange_map]
        have hV := Vf_measure (n := n) r β.vec
        have h2 := mul_le_mul_of_nonneg_left hV hκ.le
        simp only [pwf, Finset.sum_add_distrib, ← Finset.mul_sum, avgW_measure]
        linarith
      · rw [if_neg h]
        simp)
    P E (fun _ _ => trivial)
  exact h

/-! ### Sums over the branches of the unrolled run -/

section ends

variable {n Q : ℕ}

lemma start_pwf (κ : ℝ) (σ₀ : Store Var) :
    pwf κ (initBranch σ₀ : Branch Var (Fin (2 ^ n)) Q) = κ * Vf 1 1 := by
  have e : (initBranch σ₀ : Branch Var (Fin (2 ^ n)) Q).vec =
      fun _ => Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ) := rfl
  unfold pwf
  rw [e, meanV_const, avgW_const, nsq_init]
  simp [initBranch]

lemma end_pwf (κ : ℝ) (hκ : 0 ≤ κ) (E : List (Branch Var (Fin (2 ^ n)) Q)) :
    (E.map (pwf κ)).sum ≤
      κ * (Real.pi / 8 + 1 / 4) * (E.map fun β ↦ nsq (meanV β.vec)).sum +
        (E.map fun β ↦ (β.count : ℝ) * avgW β.vec).sum := by
  have h : (E.map (pwf κ)).sum ≤
      (E.map fun β ↦ (κ * (Real.pi / 8 + 1 / 4)) * nsq (meanV β.vec)
        + (β.count : ℝ) * avgW β.vec).sum := by
    refine List.sum_le_sum fun β _ => ?_
    unfold pwf
    have := Vf_le (nsq (meanV β.vec)) (avgW β.vec) (nsq_nonneg _) (nsq_meanV_le _)
    have := mul_le_mul_of_nonneg_left this hκ
    linarith
  rw [list_lin] at h
  exact h

end ends

/-! ### The theorem -/

theorem findAny_lower_bound_full : FullConstantTarget := by
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
  have hN4 : (2 : ℝ) ^ 2 ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have ht2 : (2 : ℝ) ≤ Real.sqrt (2 ^ n) := by
    apply Real.le_sqrt_of_sq_le
    norm_num at hN4 ⊢
    linarith
  set t : ℝ := Real.sqrt (2 ^ n) with htdef
  have ht0 : 0 ≤ t := by linarith
  have htsq : t ^ 2 = 2 ^ n := Real.sq_sqrt hNpos.le
  have hNnat : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
  set κ : ℝ := 2 / Real.arcsin (2 / t) with hκdef
  have hκ : 0 < κ := kappa_pos t ht2
  have hg0 : (0 : ℝ) ≤ Real.pi / 8 + 1 / 4 := by positivity
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
  have hM : ∀ M : ℕ, κ * (Real.pi / 8 + 1 / 4) ≤
      κ * (Real.pi / 8 + 1 / 4) * (2 / 2 ^ n + 2 / 2 ^ n * ∑ x, (1 - s M x)) + bound := by
    intro M
    set E := ens (GM n Q) (unroll M c) init with hE
    have h1 := pwf_ens_mono n Q t htdef ht2 (unroll M c) init
    have h2 : κ * (Real.pi / 8 + 1 / 4) ≤ (init.map (pwf κ)).sum := by
      have : (init.map (pwf κ)).sum = κ * Vf 1 1 := by
        simp only [init, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        exact start_pwf κ σ₀
      rw [this, Vf_self 1 zero_le_one, mul_one]
    have h3 := end_pwf κ hκ.le E
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
    have h9 : κ * (Real.pi / 8 + 1 / 4) * (E.map fun β ↦ nsq (meanV β.vec)).sum ≤
        κ * (Real.pi / 8 + 1 / 4) * (2 / 2 ^ n + 2 / 2 ^ n * ∑ x, (1 - s M x)) := by
      apply mul_le_mul_of_nonneg_left h4
      positivity
    linarith
  -- let the depth go to infinity
  have hlim : Tendsto (fun M ↦ ∑ x, (1 - s M x)) atTop (nhds (∑ x, (1 - L x))) := by
    refine tendsto_finsetSum _ fun x _ ↦ ?_
    exact tendsto_const_nhds.sub
      (unroll_expect_tendsto (groverParallelMarkingOracle 1 {x}) c (CQState.qSet (Δ₀ x))
        (post n Q x))
  set β : ℝ := κ * (Real.pi / 8 + 1 / 4) * (2 / 2 ^ n) with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hlim2 := hlim.const_mul β
  have hge : κ * (Real.pi / 8 + 1 / 4) - β - bound ≤ β * ∑ x, (1 - L x) := by
    refine ge_of_tendsto' hlim2 fun M ↦ ?_
    have := hM M
    have e : κ * (Real.pi / 8 + 1 / 4) * (2 / 2 ^ n + 2 / 2 ^ n * ∑ x, (1 - s M x)) =
        β + β * ∑ x, (1 - s M x) := by rw [hβ]; ring
    linarith
  have hneg : ∑ x, (1 - L x) ≤ 0 :=
    Finset.sum_nonpos fun x _ ↦ by linarith [hL x]
  have hz : β * ∑ x, (1 - L x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ0 hneg
  have hfin : κ * ((Real.pi / 8 + 1 / 4) * (1 - 2 / 2 ^ n)) ≤ bound := by
    have e : κ * ((Real.pi / 8 + 1 / 4) * (1 - 2 / 2 ^ n)) = κ * (Real.pi / 8 + 1 / 4) - β := by
      rw [hβ]; ring
    rw [e]
    linarith
  have hend := kappa_end t ht2
  rw [htsq] at hend
  show (Real.pi / 8 + 1 / 4) * t - 4 / t ≤ bound
  linarith

end GroverThreeFifths

#print axioms GroverThreeFifths.findAny_lower_bound_full
