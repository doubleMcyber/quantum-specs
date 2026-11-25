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
import LowerBounds.Grover.FindAllRevealStatement
import LowerBounds.Grover.FindAllRevealBound
import LowerBounds.Grover.FindAllRevealAverage
import LowerBounds.Grover.FindAllRevealOracle
import Mathlib

/-!
# The reveal find-all floor and its relCost floor

`findAll_floor_reveal`: every circuit with `m` slots that meets Google's find-all specification for
`k` targets, with `1 ≤ m`, `1 ≤ k` and `4 m ≤ 2 ^ n - (k - 1)`, has every accepted average cost bound
at least `(π / 8 + 1 / 4) t - 4 / t` with `t = √((2 ^ n - (k - 1)) / m)`. The hypothesis is the
plain find-all specification; the `(k - 1)`-set `K` chosen by `exists_reveal_le` appears only
inside the proof. `relCost_floor_allD : RelCostFloorAllD` follows by letting `n` grow, since
`vanillaFindAllCost n m k = (π / 4) H_k √(2 ^ n / m)` with `H_k = groverHarmonicSqrtSum k`; this
floor is non-strict.
-/

open QuantumComputation.Specs Operator ResourceCounting Filter Real
open scoped Matrix QHLExpectation ComplexOrder MatrixOrder ENNReal NNReal NNRat
open QuantumComputation.Specs.Grover (Var)
open QuantumComputation.Specs.Grover.Var (res)

namespace GroverParallel

open GroverLowerBound

/-- the reveal floor: every circuit meeting the find-all spec at (m, k) has average certified
    cost at least (π/8 + 1/4) t - 4/t, t = √((2^n - (k-1))/m) -/
theorem findAll_floor_reveal {n m k Q : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hn : 4 * m ≤ 2 ^ n - (k - 1))
    (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m))
    (hmeets : MeetsFindAllSpec k c) (bound : ℝ)
    (hbound : AvgOracleCostBound k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦ programOf c S) bound) :
    (π / 8 + 1 / 4) * √(((2 ^ n - (k - 1) : ℕ) : ℝ) / m) -
        4 / √(((2 ^ n - (k - 1) : ℕ) : ℝ) / m) ≤ bound := by
  obtain ⟨q, hq, havg⟩ := hbound
  have hkN : k ≤ 2 ^ n := by omega
  obtain ⟨K, hK, hKle⟩ := exists_reveal_le hk hkN (fun S => (q S : ℝ))
  have h := reveal_core hm hk K hK hn c hmeets
    (fun r x hx => parallelOracle_insert r K x hx)
    (fun r u => parallelOracle_single_sq_sum_le r u) q hq
  linarith

/-- The limit step: `A - 4 K / 2^n ≤ B` for all large n gives `A ≤ B`. -/
private lemma floor_coreD {A B K : ℝ} (n₀ : ℕ)
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

private lemma harm_posD {k : ℕ} (hk : 1 ≤ k) : 0 < groverHarmonicSqrtSum k := by
  unfold groverHarmonicSqrtSum
  apply Finset.sum_pos
  · intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have : (0 : ℝ) < r := by exact_mod_cast hr1
    positivity
  · exact ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, hk⟩⟩

theorem relCost_floor_allD : RelCostFloorAllD := by
  intro F hF m k hm hk hcell
  obtain ⟨hcor, hcost⟩ := hF
  obtain ⟨n₀, hn₀⟩ := hcost hcell
  have hH : 0 < groverHarmonicSqrtSum k := harm_posD hk
  have hpi : 0 < π := Real.pi_pos
  have hpi4 : π ≤ 4 := Real.pi_le_four
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set r : ℝ := ((F.relCost m k : ℚ≥0) : ℝ) with hr
  set c0 : ℝ := π / 8 + 1 / 4 with hc0
  set B : ℝ := r * (π / 4) * groverHarmonicSqrtSum k with hB
  have hc0p : 0 ≤ c0 := by positivity
  have hc01 : c0 ≤ 1 := by rw [hc0]; linarith
  have key : ∀ n : ℕ, max n₀ (4 * m + 4 * k) ≤ n →
      c0 - 4 * (((k : ℝ) + 8 * m) / 4) / (2 : ℝ) ^ n ≤ B := by
    intro n hn
    have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hn
    have hn4 : 4 * m + 4 * k ≤ n := le_trans (le_max_right _ _) hn
    have hlt : n < 2 ^ n := Nat.lt_two_pow_self
    have hkN : k ≤ 2 ^ n := by omega
    have hn1 : 1 ≤ n := by omega
    have hnD : 4 * m ≤ 2 ^ n - (k - 1) := by omega
    have hk1N : k - 1 ≤ 2 ^ n := by omega
    have h2k : 2 * k ≤ 2 ^ n := by omega
    have hb := hn₀ n hn0 hkN
    have hmeets : MeetsFindAllSpec k (F.circuit n m k) := fun S hS ↦ hcor hn1 hcell hkN hS
    have hfl := findAll_floor_reveal hm hk hnD (F.circuit n m k) hmeets _ hb
    set N : ℝ := (2 : ℝ) ^ n with hN
    set D : ℝ := (((2 ^ n - (k - 1) : ℕ)) : ℝ) with hD
    have hDc : D = N - ((k : ℝ) - 1) := by
      rw [hD, hN, Nat.cast_sub hk1N, Nat.cast_sub hk]
      push_cast
      ring
    have h2kR : 2 * (k : ℝ) ≤ N := by
      rw [hN]; exact_mod_cast h2k
    have hNpos : 0 < N := by positivity
    have hDpos : 0 < D := by rw [hDc]; linarith
    have hDN : D ≤ N := by rw [hDc]; linarith
    have hN4D : N ≤ 4 * D := by rw [hDc]; linarith
    set a : ℝ := √(D / m) with ha_def
    set s : ℝ := √(N / m) with hs_def
    have ha : 0 < a := Real.sqrt_pos.mpr (div_pos hDpos hmR)
    have hs : 0 < s := Real.sqrt_pos.mpr (div_pos hNpos hmR)
    have haa : a * a = D / m := Real.mul_self_sqrt (div_pos hDpos hmR).le
    have hss : s * s = N / m := Real.mul_self_sqrt (div_pos hNpos hmR).le
    have hsa : a ≤ s := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hDN hmR.le)
    -- s - a is small: (s - a) s ≤ (s - a)(s + a) = (k - 1)/m
    have hdiff : s * s - a * s ≤ ((k : ℝ) - 1) / m := by
      have h1 : (s - a) * s ≤ (s - a) * (s + a) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have e : (s - a) * (s + a) = ((k : ℝ) - 1) / m := by
        have e0 : (s - a) * (s + a) = s * s - a * a := by ring
        rw [e0, hss, haa, hDc]
        ring
      have e1 : (s - a) * s = s * s - a * s := by ring
      linarith
    -- s ≤ 2 a, so 4/a ≤ 8/s
    have h2a : s ≤ 2 * a := by
      have hsq : s * s ≤ (2 * a) * (2 * a) := by
        have e : (2 * a) * (2 * a) = 4 * (D / m) := by rw [← haa]; ring
        rw [e, hss, ← mul_div_assoc]
        exact div_le_div_of_nonneg_right hN4D hmR.le
      nlinarith
    have h4a : 4 / a ≤ 8 / s := by
      rw [div_le_div_iff₀ ha hs]
      linarith
    have hvan : r * vanillaFindAllCost n m k = B * s := by
      unfold vanillaFindAllCost
      rw [hB, hs_def, hN]
      ring
    rw [hvan, ← hc0] at hfl
    have h3 : c0 * a - 8 / s ≤ B * s := by linarith
    have h4 : (c0 * a - 8 / s) * s ≤ B * s * s := mul_le_mul_of_nonneg_right h3 hs.le
    have e4 : (c0 * a - 8 / s) * s = c0 * (a * s) - 8 := by field_simp
    have e5 : B * s * s = B * (N / m) := by rw [mul_assoc, hss]
    have h5 : c0 * (s * s) - c0 * (((k : ℝ) - 1) / m) ≤ c0 * (a * s) := by
      have := mul_le_mul_of_nonneg_left hdiff hc0p
      have e6 : c0 * (s * s - a * s) = c0 * (s * s) - c0 * (a * s) := by ring
      linarith
    rw [hss] at h5
    have h6 : c0 * (N / m) - c0 * (((k : ℝ) - 1) / m) - 8 ≤ B * (N / m) := by linarith
    have h7 : c0 * N - c0 * ((k : ℝ) - 1) - 8 * m ≤ B * N := by
      have := mul_le_mul_of_nonneg_left h6 hmR.le
      have e7 : (m : ℝ) * (c0 * (N / m) - c0 * (((k : ℝ) - 1) / m) - 8) =
          c0 * N - c0 * ((k : ℝ) - 1) - 8 * m := by field_simp
      have e8 : (m : ℝ) * (B * (N / m)) = B * N := by field_simp
      linarith
    have h8 : c0 * ((k : ℝ) - 1) ≤ k := by nlinarith
    have h9 : c0 * N - ((k : ℝ) + 8 * m) ≤ B * N := by linarith
    have e9 : 4 * (((k : ℝ) + 8 * m) / 4) / N = ((k : ℝ) + 8 * m) / N := by ring
    rw [e9]
    have h10 : (c0 - B) * N ≤ (k : ℝ) + 8 * m := by
      have e10 : (c0 - B) * N = c0 * N - B * N := by ring
      linarith
    have h11 : c0 - B ≤ ((k : ℝ) + 8 * m) / N := by rw [le_div_iff₀ hNpos]; exact h10
    linarith
  have hc : c0 ≤ B := floor_coreD _ key
  rw [div_le_iff₀ hH]
  have h4 : (0 : ℝ) ≤ 4 / π := by positivity
  have h5 := mul_le_mul_of_nonneg_right hc h4
  have e1 : c0 * (4 / π) = 1 / 2 + 1 / π := by rw [hc0]; field_simp; ring
  have e2 : B * (4 / π) = r * groverHarmonicSqrtSum k := by rw [hB]; field_simp
  linarith

end GroverParallel

#print axioms GroverParallel.findAll_floor_reveal
#print axioms GroverParallel.relCost_floor_allD
