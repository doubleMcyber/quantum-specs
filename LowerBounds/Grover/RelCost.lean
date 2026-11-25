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
import LowerBounds.Grover.RelCostStatement
import LowerBounds.Grover.ThreeFifthsBound
import Mathlib

/-!
# Proof of the relCost floor at cell (1, 1)

`GroverThreeFifths.relCost_floor_11 : GroverThreeFifths.RelCostFloor11`.

Take a filler that proves the challenge's two theorems and claims cell (1, 1). Its `rel_cost`
theorem gives some `n₀`. At `n = max n₀ 16` its program is an instance of the circuit quantified in
`GroverLowerBound.FindAnyLowerBound`, its correctness theorem gives `MeetsFindAnySpec`, and
`findAny_lower_bound_35` gives `(3/5) √(2^n) ≤ relCost · (π/4) √(2^n)`, so `12 / (5 π) ≤ relCost`.
Equality is impossible because `relCost` is rational and `π` is not.
-/

open QuantumComputation.Specs Operator ResourceCounting Real
open scoped NNReal NNRat

namespace GroverThreeFifths

theorem relCost_floor_11 : RelCostFloor11 := by
  intro F hF h11
  obtain ⟨hcor, hcost⟩ := hF
  obtain ⟨n₀, hn₀⟩ := hcost h11
  set n := max n₀ 16 with hndef
  have hn16 : 16 ≤ n := le_max_right _ _
  have hk : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hb := hn₀ n (le_max_left _ _) hk
  have hmeets : GroverLowerBound.MeetsFindAnySpec (F.circuit n 1 1) := by
    intro S hS
    exact hcor (by omega) h11 hk hS
  have hlow := findAny_lower_bound_35 n hn16 _ (F.circuit n 1 1) hmeets _ hb
  -- hlow : 3/5 * √(2^n) ≤ relCost 1 1 * vanillaFindAnyCost n 1 1
  have hv : vanillaFindAnyCost n 1 1 = (π / 4) * √((2 : ℝ) ^ n) := by
    simp [vanillaFindAnyCost]
  rw [hv] at hlow
  set s := √((2 : ℝ) ^ n) with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  set r : ℝ := ((F.relCost 1 1 : ℚ≥0) : ℝ) with hr
  have hpi : 0 < π := Real.pi_pos
  -- 3/5 ≤ r * π / 4
  have h1 : (3 / 5 : ℝ) ≤ r * (π / 4) := by
    have h2 : (3 / 5 : ℝ) * s ≤ (r * (π / 4)) * s := by nlinarith
    exact le_of_mul_le_mul_right h2 hspos
  have hle : (12 / (5 * π) : ℝ) ≤ r := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hne : (12 / (5 * π) : ℝ) ≠ r := by
    intro heq
    have hr0 : r ≠ 0 := by
      rw [← heq]; positivity
    have hpieq : π = ((12 / (5 * ((F.relCost 1 1 : ℚ≥0) : ℚ)) : ℚ) : ℝ) := by
      have : π = 12 / (5 * r) := by
        field_simp at heq ⊢
        linarith
      rw [this, hr]
      push_cast
      rfl
    exact irrational_pi.ne_rat _ hpieq
  exact lt_of_le_of_ne hle hne

end GroverThreeFifths

#print axioms GroverThreeFifths.relCost_floor_11
