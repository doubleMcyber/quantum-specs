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
import LowerBounds.Grover.OracleLocality
import LowerBounds.Grover.Hybrid
import LowerBounds.Grover.Mean
import LowerBounds.Grover.ParallelDefs
import Mathlib

/-!
# The one-round mean inequality over an arbitrary run index

Facts about `meanS` and `avgS` (`ParallelDefs.lean`), the Gram bound `gram_bound`, and
`mean_query_abstract`, which extends `GroverThreeFifths.mean_query` (`Mean.lean`): for self-adjoint
involutions `G i` with `∑ i ‖G i u - u‖² ≤ 4 L ‖u‖²` for every `u`, and `t² = |ι| / L`, applying
`G i` to the `i`-th run vector for every `i` lowers the norm of the mean by at most
`(2 / t²) ‖mean‖ + (2 / t) √(avgS - ‖mean‖²)`.
-/

open QuantumComputation.Specs Operator GroverLowerBound
open scoped Matrix

namespace GroverParallel

/-! ### Mean and average norm over a finite index -/

lemma meanS_eq {ι : Type} [Fintype ι] {Q : ℕ} (v : ι → Fin (2 ^ Q) → ℂ) :
    meanS v = (((Fintype.card ι : ℕ) : ℂ)⁻¹) • ∑ i, v i := by
  funext j
  simp [meanS, Finset.sum_apply]

theorem meanS_mulVec {ι : Type} [Fintype ι] {Q : ℕ} (M : Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (v : ι → Fin (2 ^ Q) → ℂ) :
    meanS (fun i => M *ᵥ v i) = M *ᵥ meanS v := by
  rw [meanS_eq, meanS_eq, Matrix.mulVec_smul, Matrix.mulVec_sum]

theorem meanS_const {ι : Type} [Fintype ι] [Nonempty ι] {Q : ℕ} (e : Fin (2 ^ Q) → ℂ) :
    meanS (fun _ : ι => e) = e := by
  funext j
  simp only [meanS, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : ((Fintype.card ι : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  exact inv_mul_cancel_left₀ this _

theorem avgS_const {ι : Type} [Fintype ι] [Nonempty ι] {Q : ℕ} (e : Fin (2 ^ Q) → ℂ) :
    avgS (fun _ : ι => e) = nsq e := by
  unfold avgS
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : ((Fintype.card ι : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  exact inv_mul_cancel_left₀ this _

theorem avgS_nonneg {ι : Type} [Fintype ι] {Q : ℕ} (v : ι → Fin (2 ^ Q) → ℂ) : 0 ≤ avgS v :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => nsq_nonneg _)

lemma sum_nsq_sub_meanS {ι : Type} [Fintype ι] [Nonempty ι] {Q : ℕ} (v : ι → Fin (2 ^ Q) → ℂ) :
    ∑ i, nsq (v i - meanS v) = ((Fintype.card ι : ℕ) : ℝ) * (avgS v - nsq (meanS v)) := by
  have hN : ((Fintype.card ι : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hNc : ((Fintype.card ι : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN
  have key : ∀ j, ∑ x, Complex.normSq (v x j - meanS v j) =
      ∑ x, Complex.normSq (v x j) - ((Fintype.card ι : ℕ) : ℝ) * Complex.normSq (meanS v j) := by
    intro j
    have hs : ∑ x, v x j = ((Fintype.card ι : ℕ) : ℂ) * meanS v j := by
      simp only [meanS]
      exact (mul_inv_cancel_left₀ hNc _).symm
    simp only [Complex.normSq_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have h1 : ∑ x : ι, (2 * (v x j * (starRingEnd ℂ) (meanS v j)).re) =
        2 * (((Fintype.card ι : ℕ) : ℝ) * Complex.normSq (meanS v j)) := by
      rw [← Finset.mul_sum, ← Complex.re_sum, ← Finset.sum_mul, hs, mul_assoc,
        Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [h1]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  unfold nsq avgS
  calc ∑ x, ∑ j, Complex.normSq (v x j - meanS v j)
      = ∑ j, ∑ x, Complex.normSq (v x j - meanS v j) := Finset.sum_comm
    _ = ∑ j, (∑ x, Complex.normSq (v x j) -
          ((Fintype.card ι : ℕ) : ℝ) * Complex.normSq (meanS v j)) :=
        Finset.sum_congr rfl fun j _ => key j
    _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_comm, mul_sub, ← mul_assoc,
          mul_inv_cancel₀ hN, one_mul]
        rfl

theorem nsq_meanS_le {ι : Type} [Fintype ι] [Nonempty ι] {Q : ℕ} (v : ι → Fin (2 ^ Q) → ℂ) :
    nsq (meanS v) ≤ avgS v := by
  have h := sum_nsq_sub_meanS v
  have hpos : (0 : ℝ) < ((Fintype.card ι : ℕ) : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  have h0 : 0 ≤ ∑ i, nsq (v i - meanS v) := Finset.sum_nonneg fun i _ => nsq_nonneg _
  rw [h] at h0
  have := nonneg_of_mul_nonneg_right h0 hpos
  linarith

/-! ### Self-inverse self-adjoint matrices preserve the norm -/

private lemma nsq_selfInv {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (hsa : M.conjTranspose = M)
    (hinv : M * M = 1) (v : Fin d → ℂ) : nsq (M *ᵥ v) = nsq v := by
  rw [nsq_mulVec, hsa, hinv, Matrix.one_mulVec, nsq_eq_dot]

theorem avgS_selfInv {ι : Type} [Fintype ι] {Q : ℕ}
    (G : ι → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (hsa : ∀ i, (G i).conjTranspose = G i) (hinv : ∀ i, G i * G i = 1)
    (v : ι → Fin (2 ^ Q) → ℂ) :
    avgS (fun i => G i *ᵥ v i) = avgS v := by
  unfold avgS
  congr 1
  exact Finset.sum_congr rfl fun i _ => nsq_selfInv (G i) (hsa i) (hinv i) (v i)

/-! ### The Gram bound -/

private lemma re_dot_le {d : ℕ} (a b : Fin d → ℂ) (c : ℝ) (hc : 0 < c) :
    2 * (star a ⬝ᵥ b).re ≤ c * nsq a + c⁻¹ * nsq b := by
  have hj : ∀ j, 2 * (star (a j) * b j).re ≤
      c * Complex.normSq (a j) + c⁻¹ * Complex.normSq (b j) := by
    intro j
    rw [← sub_nonneg]
    have e : c * Complex.normSq (a j) + c⁻¹ * Complex.normSq (b j) - 2 * (star (a j) * b j).re
        = c⁻¹ * ((c * (a j).re - (b j).re) ^ 2 + (c * (a j).im - (b j).im) ^ 2) := by
      simp only [Complex.normSq_apply, Complex.mul_re, Complex.star_def, Complex.conj_re,
        Complex.conj_im]
      field_simp <;> ring
    rw [e]
    positivity
  have h1 : (star a ⬝ᵥ b).re = ∑ j, (star (a j) * b j).re := by
    simp [dotProduct, Complex.re_sum]
  unfold nsq
  rw [h1]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => hj j

theorem gram_bound {ι : Type} [Fintype ι] {d : ℕ} (P : ι → Matrix (Fin d) (Fin d) ℂ)
    (hsa : ∀ i, (P i).conjTranspose = P i) (hid : ∀ i, P i * P i = P i) (L : ℝ)
    (hL : ∀ u : Fin d → ℂ, ∑ i, nsq (P i *ᵥ u) ≤ L * nsq u) (w : ι → Fin d → ℂ) :
    nsq (∑ i, P i *ᵥ w i) ≤ L * ∑ i, nsq (P i *ᵥ w i) := by
  obtain ⟨u, hu⟩ : ∃ u, u = ∑ i, P i *ᵥ w i := ⟨_, rfl⟩
  rw [← hu]
  have h2 : ∀ i, star u ⬝ᵥ (P i *ᵥ w i) = star (P i *ᵥ u) ⬝ᵥ (P i *ᵥ w i) := by
    intro i
    have e : star u ⬝ᵥ (P i *ᵥ w i) = star u ⬝ᵥ (P i *ᵥ (P i *ᵥ w i)) := by
      rw [Matrix.mulVec_mulVec, hid]
    have e2 : star u ⬝ᵥ (P i *ᵥ (P i *ᵥ w i)) = star (P i *ᵥ u) ⬝ᵥ (P i *ᵥ w i) := by
      rw [Matrix.star_mulVec, hsa i]
      exact Matrix.dotProduct_mulVec _ _ _
    rw [e, e2]
  have hxdot : nsq u = ∑ i, (star (P i *ᵥ u) ⬝ᵥ (P i *ᵥ w i)).re := by
    have h1 : star u ⬝ᵥ u = ∑ i, star u ⬝ᵥ (P i *ᵥ w i) := by
      rw [← dotProduct_sum, ← hu]
    rw [nsq_eq_dot, h1, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [h2 i]
  have hA := hL u
  have hxnn : 0 ≤ nsq u := nsq_nonneg _
  have hSnn : 0 ≤ ∑ i, nsq (P i *ᵥ w i) := Finset.sum_nonneg fun _ _ => nsq_nonneg _
  have key : ∀ c : ℝ, 0 < c →
      2 * nsq u ≤ c * ∑ i, nsq (P i *ᵥ u) + c⁻¹ * ∑ i, nsq (P i *ᵥ w i) := by
    intro c hc
    have h : ∑ i, 2 * (star (P i *ᵥ u) ⬝ᵥ (P i *ᵥ w i)).re ≤
        ∑ i, (c * nsq (P i *ᵥ u) + c⁻¹ * nsq (P i *ᵥ w i)) :=
      Finset.sum_le_sum fun i _ => re_dot_le (P i *ᵥ u) (P i *ᵥ w i) c hc
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h
    linarith [h, hxdot]
  by_cases hLpos : 0 < L
  · have hLi : 0 < L⁻¹ := inv_pos.2 hLpos
    have h := key L⁻¹ hLi
    rw [inv_inv] at h
    have h3 : L⁻¹ * ∑ i, nsq (P i *ᵥ u) ≤ L⁻¹ * (L * nsq u) :=
      mul_le_mul_of_nonneg_left hA hLi.le
    have e1 : L⁻¹ * (L * nsq u) = nsq u := inv_mul_cancel_left₀ hLpos.ne' _
    linarith
  · push_neg at hLpos
    have hS0 : ∀ i, nsq (P i *ᵥ w i) ≤ L * nsq (w i) := fun i =>
      (Finset.single_le_sum (f := fun j => nsq (P j *ᵥ w i)) (fun j _ => nsq_nonneg _)
        (Finset.mem_univ i)).trans (hL (w i))
    have hSle : ∑ i, nsq (P i *ᵥ w i) ≤ 0 := by
      calc ∑ i, nsq (P i *ᵥ w i) ≤ ∑ i, L * nsq (w i) := Finset.sum_le_sum fun i _ => hS0 i
        _ ≤ 0 := Finset.sum_nonpos fun i _ => by nlinarith [nsq_nonneg (w i)]
    have hS' : ∑ i, nsq (P i *ᵥ w i) = 0 := le_antisymm hSle hSnn
    have h := key 1 one_pos
    have hA' : ∑ i, nsq (P i *ᵥ u) ≤ 0 := hA.trans (by nlinarith [nsq_nonneg u])
    rw [hS'] at h ⊢
    simp only [inv_one, one_mul, mul_zero, add_zero] at h ⊢
    linarith

/-! ### The abstract one-round inequality -/

theorem mean_query_abstract {ι : Type} [Fintype ι] [Nonempty ι] {Q : ℕ}
    (G : ι → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (hsa : ∀ i, (G i).conjTranspose = G i) (hinv : ∀ i, G i * G i = 1)
    (L : ℝ) (hL : 0 < L)
    (hF2 : ∀ u : Fin (2 ^ Q) → ℂ, ∑ i, nsq (G i *ᵥ u - u) ≤ 4 * L * nsq u)
    (t : ℝ) (ht0 : 0 < t) (ht : t ^ 2 = (Fintype.card ι : ℝ) / L) (v : ι → Fin (2 ^ Q) → ℂ) :
    (1 - 2 / t ^ 2) * Real.sqrt (nsq (meanS v)) - 2 / t * Real.sqrt (avgS v - nsq (meanS v)) ≤
      Real.sqrt (nsq (meanS (fun i => G i *ᵥ v i))) := by
  -- the projectors
  obtain ⟨P, hP⟩ : ∃ P : ι → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ,
      ∀ i, P i = (((1 / 2 : ℝ) : ℂ)) • (1 - G i) := ⟨_, fun _ => rfl⟩
  have hPv : ∀ i u, P i *ᵥ u = (((1 / 2 : ℝ) : ℂ)) • (u - G i *ᵥ u) := by
    intro i u
    rw [hP i, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hPsa : ∀ i, (P i).conjTranspose = P i := by
    intro i
    rw [hP i]
    simp [Matrix.conjTranspose_smul, hsa i, Complex.star_def, Complex.conj_ofReal]
  have hPid : ∀ i, P i * P i = P i := by
    intro i
    have h := hinv i
    rw [hP i]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.one_mul, h]
    ext a b
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
    push_cast
    ring
  have hPnsq : ∀ i u, nsq (P i *ᵥ u) = (1 / 4) * nsq (G i *ᵥ u - u) := by
    intro i u
    rw [hPv, GroverThreeFifths.nsq_smul_real, GroverThreeFifths.nsq_sub_comm]
    ring
  have hLP : ∀ u : Fin (2 ^ Q) → ℂ, ∑ i, nsq (P i *ᵥ u) ≤ L * nsq u := by
    intro u
    simp only [hPnsq]
    rw [← Finset.mul_sum]
    have := hF2 u
    linarith
  have hGnsq : ∀ i (u : Fin (2 ^ Q) → ℂ), nsq (G i *ᵥ u - u) ≤ 4 * nsq u := by
    intro i u
    have h1 : nsq (G i *ᵥ u - u) ≤ 2 * nsq (G i *ᵥ u) + 2 * nsq u := by
      calc nsq (G i *ᵥ u - u)
          ≤ ∑ j, (2 * Complex.normSq ((G i *ᵥ u) j) + 2 * Complex.normSq (u j)) :=
            Finset.sum_le_sum fun j _ => normSq_sub_le _ _
        _ = 2 * nsq (G i *ᵥ u) + 2 * nsq u := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
            rfl
    rw [nsq_selfInv (G i) (hsa i) (hinv i) u] at h1
    linarith
  have hPd : ∀ i u, nsq (P i *ᵥ u) ≤ nsq u := by
    intro i u
    rw [hPnsq]
    linarith [hGnsq i u]
  -- abbreviations
  set B : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hB
  have hBpos : 0 < B := Nat.cast_pos.2 Fintype.card_pos
  set m := meanS v with hm
  set m' := meanS (fun i => G i *ᵥ v i) with hm'
  set C := nsq m with hC
  set W := avgS v with hW
  have hCW : C ≤ W := nsq_meanS_le v
  have hWC : 0 ≤ W - C := by linarith
  have hsum : ∑ i, nsq (v i - m) = B * (W - C) := sum_nsq_sub_meanS v
  have hBne : B ≠ 0 := hBpos.ne'
  have hLne : L ≠ 0 := hL.ne'
  have hsumP : ∑ i, P i *ᵥ m + ∑ i, P i *ᵥ (v i - m) =
      (((1 / 2 : ℝ) : ℂ)) • ∑ i, (v i - G i *ᵥ v i) := by
    rw [← Finset.sum_add_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Matrix.mulVec_add, add_sub_cancel, hPv]
  have hdec : m - m' = (((2 * B⁻¹ : ℝ) : ℂ)) • (∑ i, P i *ᵥ m + ∑ i, P i *ᵥ (v i - m)) := by
    rw [hsumP, smul_smul]
    have hc : (((2 * B⁻¹ : ℝ) : ℂ)) * (((1 / 2 : ℝ) : ℂ)) = ((Fintype.card ι : ℕ) : ℂ)⁻¹ := by
      rw [hB]
      push_cast
      ring
    rw [hc]
    have e1 : m' = (((Fintype.card ι : ℕ) : ℂ)⁻¹) • ∑ i, G i *ᵥ v i := meanS_eq _
    have e2 : m = (((Fintype.card ι : ℕ) : ℂ)⁻¹) • ∑ i, v i := meanS_eq _
    calc m - m' = (((Fintype.card ι : ℕ) : ℂ)⁻¹) • ∑ i, v i
          - (((Fintype.card ι : ℕ) : ℂ)⁻¹) • ∑ i, G i *ᵥ v i := by rw [← e1, ← e2]
      _ = (((Fintype.card ι : ℕ) : ℂ)⁻¹) • ∑ i, (v i - G i *ᵥ v i) := by
          rw [← smul_sub, Finset.sum_sub_distrib]
  -- the two Gram bounds
  have hAs : nsq (∑ i, P i *ᵥ m) ≤ L * (L * C) := by
    have h1 := gram_bound P hPsa hPid L hLP (fun _ => m)
    have h2 := hLP m
    have h3 : ∑ i, nsq (P i *ᵥ m) ≤ L * C := h2
    calc nsq (∑ i, P i *ᵥ m) ≤ L * ∑ i, nsq (P i *ᵥ m) := h1
      _ ≤ L * (L * C) := mul_le_mul_of_nonneg_left h3 hL.le
  have hBs : nsq (∑ i, P i *ᵥ (v i - m)) ≤ L * (B * (W - C)) := by
    have h1 := gram_bound P hPsa hPid L hLP (fun i => v i - m)
    have h3 : ∑ i, nsq (P i *ᵥ (v i - m)) ≤ B * (W - C) := by
      rw [← hsum]
      exact Finset.sum_le_sum fun i _ => hPd i _
    calc nsq (∑ i, P i *ᵥ (v i - m)) ≤ L * ∑ i, nsq (P i *ᵥ (v i - m)) := h1
      _ ≤ L * (B * (W - C)) := mul_le_mul_of_nonneg_left h3 hL.le
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.2 hBpos
  have hAr : Real.sqrt (nsq (∑ i, P i *ᵥ m)) ≤ L * Real.sqrt C := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (show 0 ≤ C from nsq_nonneg _)]
    nlinarith
  have hBr : Real.sqrt (nsq (∑ i, P i *ᵥ (v i - m))) ≤
      Real.sqrt L * Real.sqrt B * Real.sqrt (W - C) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, mul_pow, Real.sq_sqrt hL.le, Real.sq_sqrt hBpos.le, Real.sq_sqrt hWC]
    nlinarith
  have hD : Real.sqrt (nsq (m - m')) ≤
      2 * B⁻¹ * (L * Real.sqrt C + Real.sqrt L * Real.sqrt B * Real.sqrt (W - C)) := by
    rw [hdec, GroverThreeFifths.sqrt_nsq_smul_real _ (by positivity)]
    have := GroverThreeFifths.sqrt_nsq_add_le (∑ i, P i *ᵥ m) (∑ i, P i *ᵥ (v i - m))
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have htri : Real.sqrt C ≤ Real.sqrt (nsq m') + Real.sqrt (nsq (m - m')) := by
    have := GroverThreeFifths.sqrt_nsq_add_le m' (m - m')
    rwa [add_sub_cancel] at this
  -- arithmetic
  have hsLne : Real.sqrt L ≠ 0 := hsL.ne'
  have hts : t * Real.sqrt L = Real.sqrt B := by
    have htsq : t = Real.sqrt B / Real.sqrt L := by
      rw [← Real.sqrt_sq ht0.le, ht, Real.sqrt_div hBpos.le]
    rw [htsq]
    field_simp
  have hrr : Real.sqrt B * Real.sqrt B = B := Real.mul_self_sqrt hBpos.le
  have key1 : 2 * B⁻¹ * L = 2 / t ^ 2 := by
    rw [ht]
    field_simp <;> ring
  have key2 : 2 * B⁻¹ * (Real.sqrt L * Real.sqrt B) = 2 / t := by
    rw [eq_div_iff ht0.ne']
    calc 2 * B⁻¹ * (Real.sqrt L * Real.sqrt B) * t
        = 2 * B⁻¹ * ((t * Real.sqrt L) * Real.sqrt B) := by ring
      _ = 2 * B⁻¹ * (Real.sqrt B * Real.sqrt B) := by rw [hts]
      _ = 2 := by rw [hrr, mul_assoc, inv_mul_cancel₀ hBne, mul_one]
  have hD' : Real.sqrt (nsq (m - m')) ≤
      2 / t ^ 2 * Real.sqrt C + 2 / t * Real.sqrt (W - C) := by
    calc Real.sqrt (nsq (m - m'))
        ≤ 2 * B⁻¹ * (L * Real.sqrt C + Real.sqrt L * Real.sqrt B * Real.sqrt (W - C)) := hD
      _ = (2 * B⁻¹ * L) * Real.sqrt C
          + (2 * B⁻¹ * (Real.sqrt L * Real.sqrt B)) * Real.sqrt (W - C) := by ring
      _ = 2 / t ^ 2 * Real.sqrt C + 2 / t * Real.sqrt (W - C) := by rw [key1, key2]
  have : (1 - 2 / t ^ 2) * Real.sqrt C - 2 / t * Real.sqrt (W - C) =
      Real.sqrt C - (2 / t ^ 2 * Real.sqrt C + 2 / t * Real.sqrt (W - C)) := by ring
  rw [this]
  linarith

end GroverParallel

#print axioms GroverParallel.meanS_mulVec
#print axioms GroverParallel.nsq_meanS_le
#print axioms GroverParallel.meanS_const
#print axioms GroverParallel.avgS_const
#print axioms GroverParallel.gram_bound
#print axioms GroverParallel.avgS_selfInv
#print axioms GroverParallel.mean_query_abstract
