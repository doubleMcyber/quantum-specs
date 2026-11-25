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
import LowerBounds.Grover.ParallelRelCostStatement
import LowerBounds.Grover.ParallelBound
import Mathlib

/-!
# Proofs of the relCost floors at every cell

`GroverParallel.relCost_floor_any : GroverParallel.RelCostFloorAny` and
`GroverParallel.relCost_floor_all : GroverParallel.RelCostFloorAll`.

A filler that proves a challenge's obligations and claims cell `(m, k)` gives, for every large `n`,
`(π/8 + 1/4) t - 4/t ≤ bound` with `t = √(2^n / (m k))` by `fullTargetAny` or `fullTargetAll`
(`ParallelBound.lean`), where `bound = relCost * vanillaFindAnyCost n m k` (respectively
`vanillaFindAllCost`). Dividing by `t` and letting `n` grow gives the floor. For find-any,
`vanillaFindAnyCost n m k = (π/4) t`, so `1/2 + 1/π ≤ relCost`, and equality would make `π`
rational. For find-all, `vanillaFindAllCost n m k = (π/4) H √k t` with
`H = groverHarmonicSqrtSum k`, so `π/8 + 1/4 ≤ relCost (π/4) H √k`; multiplying back by `t` gives
the floor at every `n`.
-/

open QuantumComputation.Specs Operator ResourceCounting Real
open scoped NNReal NNRat

namespace GroverParallel

/-- Dividing `A t - 4/t ≤ B t` by `t > 0`. -/
private lemma half_step {A B t : ℝ} (ht : 0 < t) (h : A * t - 4 / t ≤ B * t) :
    A - 4 / t ^ 2 ≤ B := by
  have e : (A - 4 / t ^ 2) * t = A * t - 4 / t := by
    field_simp
  have h2 : (A - 4 / t ^ 2) * t ≤ B * t := by rw [e]; exact h
  exact le_of_mul_le_mul_right h2 ht

/-- The same with `t = √(x / K)`, so that `4 / t² = 4 K / x`. -/
private lemma key_of_lower {A B K x t : ℝ} (hK : 0 < K) (hx : 0 < x) (ht : t = √(x / K))
    (h : A * t - 4 / t ≤ B * t) : A - 4 * K / x ≤ B := by
  have hq : 0 < x / K := div_pos hx hK
  have htpos : 0 < t := by rw [ht]; exact Real.sqrt_pos.mpr hq
  have hsq : t ^ 2 = x / K := by rw [ht]; exact Real.sq_sqrt hq.le
  have h2 := half_step htpos h
  rwa [hsq, div_div_eq_mul_div] at h2

/-- The limit step: `A - 4 K / 2^n ≤ B` for all large n gives `A ≤ B`. -/
private lemma floor_core {A B K : ℝ} (n₀ : ℕ)
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

/-- `vanillaFindAllCost = (π/4) H_k √k t` with `t = √(2^n / (m k))`. -/
private lemma vfa_eq (n : ℕ) {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) :
    vanillaFindAllCost n m k =
      π / 4 * groverHarmonicSqrtSum k * √(k : ℝ) * √((2 : ℝ) ^ n / ((m : ℝ) * k)) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have e : (2 : ℝ) ^ n / (m : ℝ) = (k : ℝ) * ((2 : ℝ) ^ n / ((m : ℝ) * k)) := by
    field_simp
  unfold vanillaFindAllCost
  rw [e, Real.sqrt_mul (Nat.cast_nonneg k)]
  ring

theorem relCost_floor_any : RelCostFloorAny := by
  intro F hF m k hm hk hcell
  obtain ⟨hcor, hcost⟩ := hF
  obtain ⟨n₀, hn₀⟩ := hcost hcell
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hK : (0 : ℝ) < (m : ℝ) * k := mul_pos (by linarith) (by linarith)
  have hpi : 0 < π := Real.pi_pos
  have key : ∀ n : ℕ, max n₀ (n0full m k) ≤ n →
      (π / 8 + 1 / 4) - 4 * ((m : ℝ) * k) / (2 : ℝ) ^ n ≤
        ((F.relCost m k : ℚ≥0) : ℝ) * (π / 4) := by
    intro n hn
    have hn0 : n0full m k ≤ n := le_trans (le_max_right _ _) hn
    have hkN : k ≤ 2 ^ n := k_le_of_n0full hm hn0
    have hn1 : 1 ≤ n := by unfold n0full at hn0; omega
    have hb := hn₀ n (le_trans (le_max_left _ _) hn) hkN
    have hmeets : MeetsFindAnySpec k (F.circuit n m k) := fun S hS ↦ hcor hn1 hcell hkN hS
    have hlow := fullTargetAny m k hm hk n hn0 _ (F.circuit n m k) hmeets _ hb
    unfold errMK vanillaFindAnyCost at hlow
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = √((2 : ℝ) ^ n / ((m : ℝ) * k)) := ⟨_, rfl⟩
    rw [← ht] at hlow
    exact key_of_lower hK (by positivity) ht (le_of_le_of_eq hlow (by ring))
  have hc : π / 8 + 1 / 4 ≤ ((F.relCost m k : ℚ≥0) : ℝ) * (π / 4) :=
    floor_core _ key
  have hle : (1 / 2 + 1 / π : ℝ) ≤ ((F.relCost m k : ℚ≥0) : ℝ) := by
    have e : (1 / 2 + 1 / π : ℝ) = (π / 8 + 1 / 4) * (4 / π) := by
      field_simp; ring
    rw [e]
    have h4 : (0 : ℝ) ≤ 4 / π := by positivity
    have h5 := mul_le_mul_of_nonneg_right hc h4
    have e2 : ((F.relCost m k : ℚ≥0) : ℝ) * (π / 4) * (4 / π) =
        ((F.relCost m k : ℚ≥0) : ℝ) := by field_simp
    linarith
  have hne : (1 / 2 + 1 / π : ℝ) ≠ ((F.relCost m k : ℚ≥0) : ℝ) := by
    intro heq
    have hr2 : ((F.relCost m k : ℚ≥0) : ℝ) - 1 / 2 = 1 / π := by linarith
    have hpieq : π = (((((F.relCost m k : ℚ≥0) : ℚ) - 1 / 2)⁻¹ : ℚ) : ℝ) := by
      have h3 : π = (((F.relCost m k : ℚ≥0) : ℝ) - 1 / 2)⁻¹ := by
        rw [hr2, one_div, inv_inv]
      rw [h3]
      push_cast
      rfl
    exact irrational_pi.ne_rat _ hpieq
  exact lt_of_le_of_ne hle hne

theorem relCost_floor_all : RelCostFloorAll := by
  intro F hF m k hm hk hcell
  obtain ⟨hcor, hcost⟩ := hF
  obtain ⟨n₀, hn₀⟩ := hcost hcell
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hK : (0 : ℝ) < (m : ℝ) * k := mul_pos (by linarith) (by linarith)
  have key : ∀ n : ℕ, max n₀ (n0full m k) ≤ n →
      (π / 8 + 1 / 4) - 4 * ((m : ℝ) * k) / (2 : ℝ) ^ n ≤
        ((F.relCost m k : ℚ≥0) : ℝ) * (π / 4 * groverHarmonicSqrtSum k * √(k : ℝ)) := by
    intro n hn
    have hn0 : n0full m k ≤ n := le_trans (le_max_right _ _) hn
    have hkN : k ≤ 2 ^ n := k_le_of_n0full hm hn0
    have hn1 : 1 ≤ n := by unfold n0full at hn0; omega
    have hb := hn₀ n (le_trans (le_max_left _ _) hn) hkN
    have hmeets : MeetsFindAllSpec k (F.circuit n m k) := fun S hS ↦ hcor hn1 hcell hkN hS
    have hlow := fullTargetAll m k hm hk n hn0 _ (F.circuit n m k) hmeets _ hb
    unfold errMK at hlow
    rw [vfa_eq n hm hk] at hlow
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = √((2 : ℝ) ^ n / ((m : ℝ) * k)) := ⟨_, rfl⟩
    rw [← ht] at hlow
    exact key_of_lower hK (by positivity) ht (le_of_le_of_eq hlow (by ring))
  have hA : π / 8 + 1 / 4 ≤
      ((F.relCost m k : ℚ≥0) : ℝ) * (π / 4 * groverHarmonicSqrtSum k * √(k : ℝ)) :=
    floor_core _ key
  intro n
  rw [vfa_eq n hm hk]
  calc (π / 8 + 1 / 4) * √((2 : ℝ) ^ n / ((m : ℝ) * k))
      ≤ (((F.relCost m k : ℚ≥0) : ℝ) * (π / 4 * groverHarmonicSqrtSum k * √(k : ℝ))) *
          √((2 : ℝ) ^ n / ((m : ℝ) * k)) :=
        mul_le_mul_of_nonneg_right hA (Real.sqrt_nonneg _)
    _ = ((F.relCost m k : ℚ≥0) : ℝ) *
          (π / 4 * groverHarmonicSqrtSum k * √(k : ℝ) * √((2 : ℝ) ^ n / ((m : ℝ) * k))) := by
        ring

end GroverParallel

#print axioms GroverParallel.relCost_floor_any
#print axioms GroverParallel.relCost_floor_all
