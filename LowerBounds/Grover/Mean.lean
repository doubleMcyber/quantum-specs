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
import Mathlib

/-!
# The mean inequality for the Grover marking oracle (`m = 1`)

For run vectors `v x` (one per marked item `x`), `meanV v` is their mean and `avgW v` the average
squared norm. Applying the oracle `O x` to the `x`-th vector changes the mean by at most
`2 √C / N + 2 √(W - C) / √N`, where `C = ‖mean‖²`, `W = avgW`, `N = 2 ^ n`
(`GroverThreeFifths.mean_query`).
-/

open QuantumComputation.Specs Operator GroverLowerBound
open scoped Matrix

namespace GroverThreeFifths

/-- mean of the run vectors -/
noncomputable def meanV {n Q : ℕ} (v : Fin (2 ^ n) → Fin (2 ^ Q) → ℂ) : Fin (2 ^ Q) → ℂ :=
  fun j => ((2 ^ n : ℕ) : ℂ)⁻¹ * ∑ x, v x j
/-- average squared norm -/
noncomputable def avgW {n Q : ℕ} (v : Fin (2 ^ n) → Fin (2 ^ Q) → ℂ) : ℝ :=
  ((2 ^ n : ℕ) : ℝ)⁻¹ * ∑ x, nsq (v x)

/-! ### Elementary facts on `nsq` -/

lemma nsq_neg' {d : ℕ} (a : Fin d → ℂ) : nsq (-a) = nsq a := by
  simp [nsq]

lemma nsq_sub_comm {d : ℕ} (a b : Fin d → ℂ) : nsq (a - b) = nsq (b - a) := by
  rw [← neg_sub, nsq_neg']

lemma nsq_smul_real {d : ℕ} (t : ℝ) (w : Fin d → ℂ) :
    nsq ((t : ℂ) • w) = t ^ 2 * nsq w := by
  simp only [nsq, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma sqrt_nsq_smul_real {d : ℕ} (t : ℝ) (ht : 0 ≤ t) (w : Fin d → ℂ) :
    Real.sqrt (nsq ((t : ℂ) • w)) = t * Real.sqrt (nsq w) := by
  rw [nsq_smul_real, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]

lemma sqrt_nsq_add_le {d : ℕ} (a b : Fin d → ℂ) :
    Real.sqrt (nsq (a + b)) ≤ Real.sqrt (nsq a) + Real.sqrt (nsq b) := by
  have h := nrm2_add_le a b (Real.sqrt (nsq a)) (Real.sqrt (nsq b)) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (by rw [Real.sq_sqrt (nsq_nonneg a)]; exact le_rfl)
    (by rw [Real.sq_sqrt (nsq_nonneg b)]; exact le_rfl)
  exact Real.sqrt_le_iff.mpr ⟨by positivity, h⟩

/-! ### Mean and average norm -/

lemma meanV_eq {n Q : ℕ} (v : Fin (2 ^ n) → Fin (2 ^ Q) → ℂ) :
    meanV v = (((2 ^ n : ℕ) : ℂ)⁻¹) • ∑ x, v x := by
  funext j
  simp [meanV, Finset.sum_apply]

theorem meanV_mulVec {n Q : ℕ} (M : Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (v : Fin (2 ^ n) → Fin (2 ^ Q) → ℂ) :
    meanV (fun x => M *ᵥ v x) = M *ᵥ meanV v := by
  rw [meanV_eq, meanV_eq, Matrix.mulVec_smul, Matrix.mulVec_sum]

theorem avgW_unitary {n Q : ℕ} (U : Unitary (2 ^ Q)) (v : Fin (2 ^ n) → Fin (2 ^ Q) → ℂ) :
    avgW (fun x => U.1 *ᵥ v x) = avgW v := by
  unfold avgW
  rw [Finset.sum_congr rfl fun x _ => nsq_unit U (v x)]

theorem avgW_oracle {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q)
    (v : Fin (2 ^ n) → Fin (2 ^ Q) → ℂ) :
    avgW (fun x => (r.embedUnitary (groverParallelMarkingOracle 1 {x})).1 *ᵥ v x) = avgW v := by
  unfold avgW
  rw [Finset.sum_congr rfl fun x _ => nsq_unit (r.embedUnitary (groverParallelMarkingOracle 1 {x}))
    (v x)]

lemma sum_nsq_sub_mean {n Q : ℕ} (v : Fin (2 ^ n) → Fin (2 ^ Q) → ℂ) :
    ∑ x, nsq (v x - meanV v) = ((2 ^ n : ℕ) : ℝ) * (avgW v - nsq (meanV v)) := by
  have hN : ((2 ^ n : ℕ) : ℝ) ≠ 0 := by positivity
  have hNc : ((2 ^ n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN
  have key : ∀ j, ∑ x, Complex.normSq (v x j - meanV v j) =
      ∑ x, Complex.normSq (v x j) - ((2 ^ n : ℕ) : ℝ) * Complex.normSq (meanV v j) := by
    intro j
    have hs : ∑ x, v x j = ((2 ^ n : ℕ) : ℂ) * meanV v j := by
      simp only [meanV]; field_simp
    simp only [Complex.normSq_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have h1 : ∑ x : Fin (2 ^ n), (2 * (v x j * (starRingEnd ℂ) (meanV v j)).re) =
        2 * (((2 ^ n : ℕ) : ℝ) * Complex.normSq (meanV v j)) := by
      rw [← Finset.mul_sum, ← Complex.re_sum, ← Finset.sum_mul, hs, mul_assoc,
        Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [h1]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp
    ring
  unfold nsq avgW
  calc ∑ x, ∑ j, Complex.normSq (v x j - meanV v j)
      = ∑ j, ∑ x, Complex.normSq (v x j - meanV v j) := Finset.sum_comm
    _ = ∑ j, (∑ x, Complex.normSq (v x j) -
          ((2 ^ n : ℕ) : ℝ) * Complex.normSq (meanV v j)) :=
        Finset.sum_congr rfl fun j _ => key j
    _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_comm, mul_sub, ← mul_assoc,
          mul_inv_cancel₀ hN, one_mul]
        rfl

theorem nsq_meanV_le {n Q : ℕ} (v : Fin (2 ^ n) → Fin (2 ^ Q) → ℂ) :
    nsq (meanV v) ≤ avgW v := by
  have h := sum_nsq_sub_mean v
  have hpos : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ) := by positivity
  have h0 : 0 ≤ ∑ x, nsq (v x - meanV v) := Finset.sum_nonneg fun x _ => nsq_nonneg _
  rw [h] at h0
  have := nonneg_of_mul_nonneg_right h0 hpos
  linarith

/-! ### Disjoint supports -/

lemma diff_zero {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) (w : Fin (2 ^ Q) → ℂ)
    (x : Fin (2 ^ n)) (i : Fin (2 ^ Q)) (h : addr r i ≠ x) :
    (w - (r.embedUnitary (groverParallelMarkingOracle 1 {x})).1 *ᵥ w) i = 0 := by
  rw [Pi.sub_apply, oracle_apply_of_addr_ne r x w i h, sub_self]

lemma nsq_sum_disjoint {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q)
    (F : Fin (2 ^ n) → Fin (2 ^ Q) → ℂ) (hF : ∀ x i, addr r i ≠ x → F x i = 0) :
    nsq (∑ x, F x) = ∑ x, nsq (F x) := by
  unfold nsq
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (∑ x, F x) i = F (addr r i) i := by
    rw [Finset.sum_apply]
    exact Finset.sum_eq_single _ (fun x _ hx => hF x i (Ne.symm hx)) (by simp)
  rw [h1]
  exact (Finset.sum_eq_single (f := fun x => Complex.normSq (F x i)) (addr r i)
    (fun x _ hx => by simp only [hF x i (Ne.symm hx), map_zero]) (by simp)).symm

lemma nsq_sub_oracle_le {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) (x : Fin (2 ^ n))
    (w : Fin (2 ^ Q) → ℂ) :
    nsq (w - (r.embedUnitary (groverParallelMarkingOracle 1 {x})).1 *ᵥ w) ≤ 4 * nsq w := by
  have h : nsq ((r.embedUnitary (groverParallelMarkingOracle 1 {x})).1 *ᵥ w) = nsq w :=
    nsq_unit _ w
  calc nsq (w - (r.embedUnitary (groverParallelMarkingOracle 1 {x})).1 *ᵥ w)
      ≤ ∑ j, (2 * Complex.normSq (w j) +
          2 * Complex.normSq (((r.embedUnitary (groverParallelMarkingOracle 1 {x})).1 *ᵥ w) j)) :=
        Finset.sum_le_sum fun j _ => normSq_sub_le _ _
    _ = 4 * nsq w := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        have : ∑ j, Complex.normSq
            (((r.embedUnitary (groverParallelMarkingOracle 1 {x})).1 *ᵥ w) j) = nsq w := by
          rw [← h]; rfl
        rw [this]
        show 2 * nsq w + 2 * nsq w = 4 * nsq w
        ring

/-! ### The mean inequality -/

theorem mean_query {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q)
    (v : Fin (2 ^ n) → Fin (2 ^ Q) → ℂ) :
    (1 - 2 / Real.sqrt (2 ^ n) ^ 2) * Real.sqrt (nsq (meanV v))
      - 2 / Real.sqrt (2 ^ n) * Real.sqrt (avgW v - nsq (meanV v))
      ≤ Real.sqrt (nsq (meanV (fun x =>
          (r.embedUnitary (groverParallelMarkingOracle 1 {x})).1 *ᵥ v x))) := by
  -- abbreviations
  set N : ℝ := ((2 ^ n : ℕ) : ℝ) with hNdef
  set m := meanV v with hm
  set m' := meanV (fun x => (r.embedUnitary (groverParallelMarkingOracle 1 {x})).1 *ᵥ v x)
    with hm'
  set O : Fin (2 ^ n) → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ :=
    fun x => (r.embedUnitary (groverParallelMarkingOracle 1 {x})).1 with hO
  have hNpos : 0 < N := by positivity
  have hNc : ((2 ^ n : ℕ) : ℂ)⁻¹ = ((N⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv, hNdef, Complex.ofReal_natCast]
  set C := nsq m with hC
  set W := avgW v with hW
  have hCW : C ≤ W := nsq_meanV_le v
  have hsum := sum_nsq_sub_mean v
  -- the three families
  set A : Fin (2 ^ n) → Fin (2 ^ Q) → ℂ := fun x => m - O x *ᵥ m with hA
  set B : Fin (2 ^ n) → Fin (2 ^ Q) → ℂ :=
    fun x => (v x - m) - O x *ᵥ (v x - m) with hB
  have hdec : m - m' = ((N⁻¹ : ℝ) : ℂ) • (∑ x, A x + ∑ x, B x) := by
    have e1 : m' = (((2 ^ n : ℕ) : ℂ)⁻¹) • ∑ x, O x *ᵥ v x := meanV_eq _
    have e2 : m = (((2 ^ n : ℕ) : ℂ)⁻¹) • ∑ x, v x := meanV_eq _
    have hpt : ∀ x, v x - O x *ᵥ v x = A x + B x := by
      intro x
      simp only [hA, hB, Matrix.mulVec_sub]
      abel
    rw [← hNc]
    calc m - m' = (((2 ^ n : ℕ) : ℂ)⁻¹) • ∑ x, v x
          - (((2 ^ n : ℕ) : ℂ)⁻¹) • ∑ x, O x *ᵥ v x := by rw [← e1, ← e2]
      _ = (((2 ^ n : ℕ) : ℂ)⁻¹) • ∑ x, (v x - O x *ᵥ v x) := by
          rw [← smul_sub, Finset.sum_sub_distrib]
      _ = (((2 ^ n : ℕ) : ℂ)⁻¹) • (∑ x, A x + ∑ x, B x) := by
          rw [← Finset.sum_add_distrib]
          congr 1
          exact Finset.sum_congr rfl fun x _ => hpt x
  have hAs : nsq (∑ x, A x) ≤ 4 * C := by
    have hdis : nsq (∑ x, A x) = ∑ x, nsq (A x) :=
      nsq_sum_disjoint r A fun x i h => diff_zero r m x i h
    rw [hdis]
    calc ∑ x, nsq (A x) = ∑ x, nsq (O x *ᵥ m - m) :=
          Finset.sum_congr rfl fun x _ => nsq_sub_comm _ _
      _ ≤ 4 * nsq m := oracle_sq_sum_le r m
  have hBs : nsq (∑ x, B x) ≤ 4 * (N * (W - C)) := by
    have hdis : nsq (∑ x, B x) = ∑ x, nsq (B x) :=
      nsq_sum_disjoint r B fun x i h => diff_zero r (v x - m) x i h
    rw [hdis, ← hsum, Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => nsq_sub_oracle_le r x (v x - m)
  have hWC : 0 ≤ W - C := by linarith
  have hAr : Real.sqrt (nsq (∑ x, A x)) ≤ 2 * Real.sqrt C := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (nsq_nonneg _)]
    nlinarith
  have hBr : Real.sqrt (nsq (∑ x, B x)) ≤ 2 * (Real.sqrt N * Real.sqrt (W - C)) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, mul_pow, Real.sq_sqrt hNpos.le, Real.sq_sqrt hWC]
    nlinarith
  have hD : Real.sqrt (nsq (m - m')) ≤
      N⁻¹ * (2 * Real.sqrt C + 2 * (Real.sqrt N * Real.sqrt (W - C))) := by
    rw [hdec, sqrt_nsq_smul_real _ (by positivity)]
    have := sqrt_nsq_add_le (∑ x, A x) (∑ x, B x)
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have htri : Real.sqrt C ≤ Real.sqrt (nsq m') + Real.sqrt (nsq (m - m')) := by
    have := sqrt_nsq_add_le m' (m - m')
    rwa [add_sub_cancel] at this
  -- arithmetic
  set s := Real.sqrt N with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr hNpos
  have hs2 : s ^ 2 = N := Real.sq_sqrt hNpos.le
  have hs2' : Real.sqrt (2 ^ n) ^ 2 = N := by
    rw [hNdef]; push_cast; exact Real.sq_sqrt (by positivity)
  have hs' : Real.sqrt (2 ^ n) = s := by
    rw [hs, hNdef]; push_cast; rfl
  rw [hs2', hs']
  have key : N⁻¹ * (2 * Real.sqrt C + 2 * (s * Real.sqrt (W - C))) =
      2 / N * Real.sqrt C + 2 / s * Real.sqrt (W - C) := by
    rw [← hs2]
    field_simp
  have : (1 - 2 / N) * Real.sqrt C - 2 / s * Real.sqrt (W - C) =
      Real.sqrt C - (2 / N * Real.sqrt C + 2 / s * Real.sqrt (W - C)) := by ring
  rw [this, ← key]
  linarith

end GroverThreeFifths

#print axioms GroverThreeFifths.nsq_meanV_le
#print axioms GroverThreeFifths.avgW_oracle
#print axioms GroverThreeFifths.mean_query
#print axioms GroverThreeFifths.meanV_mulVec
#print axioms GroverThreeFifths.avgW_unitary
