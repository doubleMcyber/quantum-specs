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
import LowerBounds.Grover.RelCostFullStatement
import LowerBounds.Grover.FullBound
import Mathlib

/-!
# Proof of the sharp relCost floor at cell (1, 1)

`GroverThreeFifths.relCost_floor_11_full : GroverThreeFifths.RelCostFloor11Full`.

Take a filler that proves the challenge's two theorems and claims cell (1, 1). For every large `n`,
`findAny_lower_bound_full` (`FullBound.lean`) gives
`(π/8 + 1/4) √(2^n) - 4/√(2^n) ≤ relCost · (π/4) √(2^n)`. Dividing by `√(2^n)` and letting `n` grow
gives `π/8 + 1/4 ≤ relCost · π/4`, that is `1/2 + 1/π ≤ relCost`. Equality is impossible because
`relCost` is rational and `π` is not.
-/

open QuantumComputation.Specs Operator ResourceCounting Real
open scoped NNReal NNRat

namespace GroverThreeFifths

theorem relCost_floor_11_full : RelCostFloor11Full := by
  intro F hF h11
  obtain ⟨hcor, hcost⟩ := hF
  obtain ⟨n₀, hn₀⟩ := hcost h11
  set r : ℝ := ((F.relCost 1 1 : ℚ≥0) : ℝ) with hr
  have hpi : 0 < π := Real.pi_pos
  -- for every n ≥ max n₀ 2: π/8 + 1/4 - 4 / 2^n ≤ r * (π / 4)
  have key : ∀ n : ℕ, max n₀ 2 ≤ n →
      (π / 8 + 1 / 4) - 4 / (2 : ℝ) ^ n ≤ r * (π / 4) := by
    intro n hn
    have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
    have hk : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hb := hn₀ n (le_trans (le_max_left _ _) hn) hk
    have hmeets : GroverLowerBound.MeetsFindAnySpec (F.circuit n 1 1) := by
      intro S hS
      exact hcor (by omega) h11 hk hS
    have hlow := findAny_lower_bound_full n hn2 _ (F.circuit n 1 1) hmeets _ hb
    have hv : vanillaFindAnyCost n 1 1 = (π / 4) * √((2 : ℝ) ^ n) := by
      simp [vanillaFindAnyCost]
    rw [hv] at hlow
    have hN : (0 : ℝ) < 2 ^ n := by positivity
    set s := √((2 : ℝ) ^ n) with hs
    have hspos : 0 < s := Real.sqrt_pos.mpr hN
    have hss : s * s = (2 : ℝ) ^ n := Real.mul_self_sqrt hN.le
    -- hlow : (π/8 + 1/4) * s - 4 / s ≤ r * (π / 4 * s)
    have h1 : ((π / 8 + 1 / 4) - 4 / (2 : ℝ) ^ n) * s ≤ (r * (π / 4)) * s := by
      have e : ((π / 8 + 1 / 4) - 4 / (2 : ℝ) ^ n) * s = (π / 8 + 1 / 4) * s - 4 / s := by
        rw [← hss]; field_simp
      rw [e]
      have e2 : (r * (π / 4)) * s = r * (π / 4 * s) := by ring
      rw [e2]
      beta_reduce at hlow
      exact hlow
    exact le_of_mul_le_mul_right h1 hspos
  have hc : π / 8 + 1 / 4 ≤ r * (π / 4) := by
    by_contra hcon
    push_neg at hcon
    set ε := π / 8 + 1 / 4 - r * (π / 4) with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    obtain ⟨M, hM⟩ := exists_nat_gt (4 / ε)
    set n := max (max n₀ 2) M with hndef
    have hk := key n (le_max_left _ _)
    have hMn : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_max_right _ _
    have hn2 : (n : ℝ) < (2 : ℝ) ^ n := by exact_mod_cast Nat.lt_two_pow_self
    have hbig : 4 / ε < (2 : ℝ) ^ n := by linarith
    have hsmall : 4 / (2 : ℝ) ^ n < ε := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hεpos] at hbig
      linarith
    linarith
  have hle : (1 / 2 + 1 / π : ℝ) ≤ r := by
    have e : (1 / 2 + 1 / π : ℝ) = (π / 8 + 1 / 4) * (4 / π) := by
      field_simp; ring
    rw [e]
    have h4 : (0 : ℝ) ≤ 4 / π := by positivity
    have := mul_le_mul_of_nonneg_right hc h4
    have e2 : r * (π / 4) * (4 / π) = r := by field_simp
    linarith
  have hne : (1 / 2 + 1 / π : ℝ) ≠ r := by
    intro heq
    have hr2 : r - 1 / 2 = 1 / π := by linarith
    have hpieq : π = (((((F.relCost 1 1 : ℚ≥0) : ℚ) - 1 / 2)⁻¹ : ℚ) : ℝ) := by
      have : π = (r - 1 / 2)⁻¹ := by rw [hr2, one_div, inv_inv]
      rw [this, hr]
      push_cast
      rfl
    exact irrational_pi.ne_rat _ hpieq
  exact lt_of_le_of_ne hle hne

end GroverThreeFifths

#print axioms GroverThreeFifths.relCost_floor_11_full
