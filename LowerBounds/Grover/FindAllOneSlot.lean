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
import LowerBounds.Grover.FindAllOneSlotStatement
import LowerBounds.Grover.FindAllOneSlotBound
import LowerBounds.Grover.FindAllFLLower
import Mathlib

/-!
# Proof of the one-slot find-all relCost floor

`GroverParallel.relCost_floor_allB : GroverParallel.RelCostFloorAllB`. A filler that solves
find-all and claims `(1, k)` gives, at every large `n`, a one-slot circuit with accepted bound
`relCost 1 k * vanillaFindAllCost n 1 k`. `findAll_floor_FL` and `FL_lower` bound it from below by
`(1 / 2 - 2 k / 2 ^ n) H_k √(2 ^ n)`, with `H_k = groverHarmonicSqrtSum k`, and
`vanillaFindAllCost n 1 k = (π / 4) H_k √(2 ^ n)`. Letting `n` grow gives `2 / π ≤ relCost 1 k`,
and equality would make `π` rational.
-/

open QuantumComputation.Specs Operator ResourceCounting Real
open scoped NNReal NNRat

namespace GroverParallel

/-- The limit step: `A - 4 K / 2^n ≤ B` for all large n gives `A ≤ B`. -/
private lemma floor_coreB {A B K : ℝ} (n₀ : ℕ)
    (key : ∀ n : ℕ, n₀ ≤ n → A - 4 * K / (2 : ℝ) ^ n ≤ B) : A ≤ B := by
  by_contra hcon
  have hε : 0 < A - B := sub_pos.mpr (not_le.mp hcon)
  obtain ⟨M, hM⟩ := exists_nat_gt (4 * K / (A - B))
  have hk := key (max n₀ M) (le_max_left _ _)
  have hMn : (M : ℝ) ≤ ((max n₀ M : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
  have hn2 : ((max n₀ M : ℕ) : ℝ) < (2 : ℝ) ^ (max n₀ M) := by
    exact_mod_cast Nat.lt_two_pow_self
  have hbig : 4 * K / (A - B) < (2 : ℝ) ^ (max n₀ M) := by linarith
  have hsmall : 4 * K / (2 : ℝ) ^ (max n₀ M) < A - B := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hbig
    linarith
  linarith

private lemma harm_pos {k : ℕ} (hk : 1 ≤ k) : 0 < groverHarmonicSqrtSum k := by
  unfold groverHarmonicSqrtSum
  apply Finset.sum_pos
  · intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have : (0 : ℝ) < r := by exact_mod_cast hr1
    positivity
  · exact ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, hk⟩⟩

theorem relCost_floor_allB : RelCostFloorAllB := by
  intro F hF k hk hcell
  obtain ⟨hcor, hcost⟩ := hF
  obtain ⟨n₀, hn₀⟩ := hcost hcell
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hH : 0 < groverHarmonicSqrtSum k := harm_pos hk
  have hpi : 0 < π := Real.pi_pos
  have key : ∀ n : ℕ, max n₀ (4 * k) ≤ n →
      (1 / 2 : ℝ) - 4 * ((k : ℝ) / 2) / (2 : ℝ) ^ n ≤
        ((F.relCost 1 k : ℚ≥0) : ℝ) * (π / 4) := by
    intro n hn
    have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hn
    have hn4 : 4 * k ≤ n := le_trans (le_max_right _ _) hn
    have hlt : n < 2 ^ n := Nat.lt_two_pow_self
    have h4N : 4 * k ≤ 2 ^ n := by omega
    have hkN : k ≤ 2 ^ n := by omega
    have h2N : 2 * k ≤ 2 ^ n := by omega
    have hn1 : 1 ≤ n := by omega
    have hb := hn₀ n hn0 hkN
    have hmeets : MeetsFindAllSpec k (F.circuit n 1 k) := fun S hS ↦ hcor hn1 hcell hkN hS
    have hFL := findAll_floor_FL hk h2N (F.circuit n 1 k) hmeets _ hb
    have hlow := FL_lower (2 ^ n) k hk h4N
    have hNR : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ) := by positivity
    have hsq : 0 < √(((2 ^ n : ℕ) : ℝ)) := Real.sqrt_pos.mpr hNR
    have hP : 0 < groverHarmonicSqrtSum k * √(((2 ^ n : ℕ) : ℝ)) := mul_pos hH hsq
    have hcast : (((2 ^ n : ℕ)) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
    have hvan : vanillaFindAllCost n 1 k =
        π / 4 * groverHarmonicSqrtSum k * √(((2 ^ n : ℕ) : ℝ)) := by
      unfold vanillaFindAllCost
      rw [hcast]
      simp
    rw [hvan] at hFL
    have h1 : ((1 / 2 : ℝ) - 2 * (k : ℝ) / ((2 ^ n : ℕ) : ℝ)) *
        (groverHarmonicSqrtSum k * √(((2 ^ n : ℕ) : ℝ))) ≤
        (((F.relCost 1 k : ℚ≥0) : ℝ) * (π / 4)) *
          (groverHarmonicSqrtSum k * √(((2 ^ n : ℕ) : ℝ))) := by
      calc _ = (1 / 2 - 2 * (k : ℝ) / ((2 ^ n : ℕ) : ℝ)) * groverHarmonicSqrtSum k *
              √(((2 ^ n : ℕ) : ℝ)) := by ring
        _ ≤ _ := hlow
        _ ≤ _ := hFL
        _ = _ := by ring
    have h2 := le_of_mul_le_mul_right h1 hP
    rw [hcast] at h2
    have e : 4 * ((k : ℝ) / 2) / (2 : ℝ) ^ n = 2 * (k : ℝ) / (2 : ℝ) ^ n := by ring
    rw [e]
    exact h2
  have hc : (1 / 2 : ℝ) ≤ ((F.relCost 1 k : ℚ≥0) : ℝ) * (π / 4) := floor_coreB _ key
  have hle : (2 / π : ℝ) ≤ ((F.relCost 1 k : ℚ≥0) : ℝ) := by
    have e : (2 / π : ℝ) = (1 / 2) * (4 / π) := by field_simp; norm_num
    rw [e]
    have h4 : (0 : ℝ) ≤ 4 / π := by positivity
    have h5 := mul_le_mul_of_nonneg_right hc h4
    have e2 : ((F.relCost 1 k : ℚ≥0) : ℝ) * (π / 4) * (4 / π) =
        ((F.relCost 1 k : ℚ≥0) : ℝ) := by field_simp
    linarith
  have hne : (2 / π : ℝ) ≠ ((F.relCost 1 k : ℚ≥0) : ℝ) := by
    intro heq
    have hr0 : ((F.relCost 1 k : ℚ≥0) : ℝ) ≠ 0 := by
      rw [← heq]; positivity
    have h3 : π = 2 / ((F.relCost 1 k : ℚ≥0) : ℝ) := by
      rw [← heq]; field_simp
    have hpieq : π = (((2 / ((F.relCost 1 k : ℚ≥0) : ℚ) : ℚ)) : ℝ) := by
      rw [h3]
      push_cast
      rfl
    exact irrational_pi.ne_rat _ hpieq
  exact lt_of_le_of_ne hle hne

end GroverParallel

#print axioms GroverParallel.relCost_floor_allB
