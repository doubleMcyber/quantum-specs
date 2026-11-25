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
import LowerBounds.Grover.FindAllSlotsStatement
import LowerBounds.Grover.FindAllOneSlotBound
import LowerBounds.Grover.FindAllFloorCoreSlots
import LowerBounds.Grover.FindAllOracleSlots
import LowerBounds.Grover.FindAllFLLower
import Mathlib

/-!
# The `m`-slot find-all floor and its relCost floor

`findAll_floor_FL_m`: every circuit with `m` slots that meets Google's find-all specification for
`k` targets, with `1 ≤ m`, `1 ≤ k` and `2 k ≤ 2 ^ n`, has every accepted average cost bound
satisfy `FL (2 ^ n) (k - 1) ≤ m * bound`. The proof applies `fa_floor_core_m` to `Ypot / m`.
`relCost_floor_allC : RelCostFloorAllC` follows with `FL_lower` by letting `n` grow, since
`vanillaFindAllCost n m k = (π / 4) H_k √(2 ^ n / m)` with `H_k = groverHarmonicSqrtSum k`; this
floor is non-strict.
-/

open QuantumComputation.Specs Operator ResourceCounting Filter Real
open scoped Matrix QHLExpectation ComplexOrder MatrixOrder ENNReal NNReal NNRat
open QuantumComputation.Specs.Grover (Var)
open QuantumComputation.Specs.Grover.Var (res)

namespace GroverParallel

open GroverLowerBound

/-- the find-all floor at m slots: every circuit meeting the find-all spec for k targets
    has average cost at least F_L(2^n, k - 1) / m -/
theorem findAll_floor_FL_m {n m k Q : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (hN : 2 * k ≤ 2 ^ n)
    (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m))
    (hmeets : MeetsFindAllSpec k c) (bound : ℝ)
    (hbound : AvgOracleCostBound k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦ programOf c S) bound) :
    FL (2 ^ n) (k - 1) ≤ (m : ℝ) * bound := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hk
  have hN' : 2 * (k' + 1) ≤ Fintype.card (Fin (2 ^ n)) := by
    rw [Fintype.card_fin]; exact hN
  have hkN : k' + 1 ≤ 2 ^ n := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hY0 : ∀ x : Fin (2 ^ n), HY (d := 2 ^ Q)
      (fun S S' => Ypot (Fin (2 ^ n)) k' (kEquiv n (k' + 1) S) (kEquiv n (k' + 1) S'))
      (signX x) := fun x => by
    have h := HY_reindex (d := 2 ^ Q) (kEquiv n (k' + 1)) _ _
      (Ypot_HY (Fin (2 ^ n)) k' hN' x (d := 2 ^ Q))
    exact h
  have hcore := fa_floor_core_m (n := n) (m := m) (k := k' + 1) (Q := Q) hk hkN c hmeets
    (fun S S' => Ypot (Fin (2 ^ n)) k' (kEquiv n (k' + 1) S) (kEquiv n (k' + 1) S') / m)
    (fun i r v => hH_multi_scaled hm _ hY0 i r v)
    (fun S => by
      show Ypot (Fin (2 ^ n)) k' (kEquiv n (k' + 1) S) (kEquiv n (k' + 1) S) / m ≤ 0
      rw [Ypot_diag, zero_div])
    bound hbound
  have key : ∀ F : lev (Fin (2 ^ n)) (k' + 1) → lev (Fin (2 ^ n)) (k' + 1) → ℝ,
      ∑ S, ∑ S', F (kEquiv n (k' + 1) S) (kEquiv n (k' + 1) S') = ∑ T, ∑ T', F T T' :=
    fun F =>
      (Finset.sum_congr rfl fun S _ => Equiv.sum_comp (kEquiv n (k' + 1)) (fun T' => F _ T')).trans
        (Equiv.sum_comp (kEquiv n (k' + 1)) (fun T => ∑ T', F T T'))
  have hkey := key (fun T T' => Ypot (Fin (2 ^ n)) k' T T' / m)
  rw [hkey] at hcore
  have hdiv : ∑ T, ∑ T', Ypot (Fin (2 ^ n)) k' T T' / (m : ℝ) =
      (∑ T, ∑ T', Ypot (Fin (2 ^ n)) k' T T') / m := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun T _ => (Finset.sum_div _ _ _).symm
  rw [hdiv, Ypot_sum _ _ hN', Fintype.card_fin, div_le_iff₀ hmR] at hcore
  have hpos : (0 : ℝ) < ((2 ^ n).choose (k' + 1) : ℕ) := by
    exact_mod_cast Nat.choose_pos hkN
  rw [Nat.add_sub_cancel]
  have h2 : ((2 ^ n).choose (k' + 1) : ℝ) * FL (2 ^ n) k' ≤
      ((2 ^ n).choose (k' + 1) : ℝ) * ((m : ℝ) * bound) := by
    calc _ ≤ ((2 ^ n).choose (k' + 1) : ℝ) * bound * m := hcore
      _ = _ := by ring
  exact le_of_mul_le_mul_left h2 hpos

/-- The limit step: `A - 4 K / 2^n ≤ B` for all large n gives `A ≤ B`. -/
private lemma floor_coreC {A B K : ℝ} (n₀ : ℕ)
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

private lemma harm_posC {k : ℕ} (hk : 1 ≤ k) : 0 < groverHarmonicSqrtSum k := by
  unfold groverHarmonicSqrtSum
  apply Finset.sum_pos
  · intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have : (0 : ℝ) < r := by exact_mod_cast hr1
    positivity
  · exact ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, hk⟩⟩

theorem relCost_floor_allC : RelCostFloorAllC := by
  intro F hF m k hm hk hcell
  obtain ⟨hcor, hcost⟩ := hF
  obtain ⟨n₀, hn₀⟩ := hcost hcell
  have hH : 0 < groverHarmonicSqrtSum k := harm_posC hk
  have hpi : 0 < π := Real.pi_pos
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsm : 0 < √(m : ℝ) := Real.sqrt_pos.mpr hmR
  have hsm2 : √(m : ℝ) * √(m : ℝ) = m := Real.mul_self_sqrt hmR.le
  set r : ℝ := ((F.relCost m k : ℚ≥0) : ℝ) with hr
  have key : ∀ n : ℕ, max n₀ (4 * k) ≤ n →
      (1 / 2 : ℝ) - 4 * ((k : ℝ) / 2) / (2 : ℝ) ^ n ≤ √(m : ℝ) * r * (π / 4) := by
    intro n hn
    have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hn
    have hn4 : 4 * k ≤ n := le_trans (le_max_right _ _) hn
    have hlt : n < 2 ^ n := Nat.lt_two_pow_self
    have h4N : 4 * k ≤ 2 ^ n := by omega
    have hkN : k ≤ 2 ^ n := by omega
    have h2N : 2 * k ≤ 2 ^ n := by omega
    have hn1 : 1 ≤ n := by omega
    have hb := hn₀ n hn0 hkN
    have hmeets : MeetsFindAllSpec k (F.circuit n m k) := fun S hS ↦ hcor hn1 hcell hkN hS
    have hFL := findAll_floor_FL_m hm hk h2N (F.circuit n m k) hmeets _ hb
    have hlow := FL_lower (2 ^ n) k hk h4N
    have hNR : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ) := by positivity
    have hsq : 0 < √(((2 ^ n : ℕ) : ℝ)) := Real.sqrt_pos.mpr hNR
    have hP : 0 < groverHarmonicSqrtSum k * √(((2 ^ n : ℕ) : ℝ)) := mul_pos hH hsq
    have hcast : (((2 ^ n : ℕ)) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
    -- √(N/m) * m = √m * √N
    have hsqm : √((2 : ℝ) ^ n / m) * m = √(m : ℝ) * √(((2 ^ n : ℕ) : ℝ)) := by
      rw [Real.sqrt_div' _ hmR.le, hcast]
      field_simp
      linarith [Real.sq_sqrt hmR.le]
    have hvan : (m : ℝ) * (r * vanillaFindAllCost n m k) =
        (√(m : ℝ) * r * (π / 4)) * (groverHarmonicSqrtSum k * √(((2 ^ n : ℕ) : ℝ))) := by
      unfold vanillaFindAllCost
      calc (m : ℝ) * (r * (π / 4 * groverHarmonicSqrtSum k * √((2 : ℝ) ^ n / m)))
          = r * (π / 4) * groverHarmonicSqrtSum k * (√((2 : ℝ) ^ n / m) * m) := by ring
        _ = _ := by rw [hsqm]; ring
    have h1 : ((1 / 2 : ℝ) - 2 * (k : ℝ) / ((2 ^ n : ℕ) : ℝ)) *
        (groverHarmonicSqrtSum k * √(((2 ^ n : ℕ) : ℝ))) ≤
        (√(m : ℝ) * r * (π / 4)) * (groverHarmonicSqrtSum k * √(((2 ^ n : ℕ) : ℝ))) := by
      calc _ = (1 / 2 - 2 * (k : ℝ) / ((2 ^ n : ℕ) : ℝ)) * groverHarmonicSqrtSum k *
              √(((2 ^ n : ℕ) : ℝ)) := by ring
        _ ≤ _ := hlow
        _ ≤ _ := hFL
        _ = _ := hvan
    have h2 := le_of_mul_le_mul_right h1 hP
    rw [hcast] at h2
    have e : 4 * ((k : ℝ) / 2) / (2 : ℝ) ^ n = 2 * (k : ℝ) / (2 : ℝ) ^ n := by ring
    rw [e]
    exact h2
  have hc : (1 / 2 : ℝ) ≤ √(m : ℝ) * r * (π / 4) := floor_coreC _ key
  rw [div_le_iff₀ hsm]
  have e : (2 / π : ℝ) = (1 / 2) * (4 / π) := by field_simp; norm_num
  rw [e]
  have h4 : (0 : ℝ) ≤ 4 / π := by positivity
  have h5 := mul_le_mul_of_nonneg_right hc h4
  have e2 : √(m : ℝ) * r * (π / 4) * (4 / π) = r * √(m : ℝ) := by field_simp
  linarith

end GroverParallel

#print axioms GroverParallel.findAll_floor_FL_m
#print axioms GroverParallel.relCost_floor_allC
