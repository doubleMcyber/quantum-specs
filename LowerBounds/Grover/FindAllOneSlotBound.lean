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
import LowerBounds.Grover.FindAllFloorCore
import LowerBounds.Grover.FindAllJohnsonPotentialDrop
import LowerBounds.Grover.FindAllJohnsonPotentialValue
import Mathlib

/-!
# The one-slot find-all floor `FL`

`findAll_floor_FL`: every one-slot circuit that meets Google's find-all specification for `k`
targets among `2 ^ n` addresses, with `1 ≤ k` and `2 k ≤ 2 ^ n`, has every accepted average cost
bound at least `FL (2 ^ n) (k - 1)`. The proof identifies the `k`-sets with `lev (Fin (2 ^ n)) k`
(`kEquiv`), takes `Y = Ypot` and combines `fa_floor_core` with `Ypot_HY`, `Ypot_diag` and
`Ypot_sum`.
-/

open QuantumComputation.Specs Operator ResourceCounting Filter Real
open scoped Matrix QHLExpectation ComplexOrder MatrixOrder ENNReal NNReal
open QuantumComputation.Specs.Grover (Var)
open QuantumComputation.Specs.Grover.Var (res)

namespace GroverParallel

open GroverLowerBound

/-- KSet and lev are the same type up to the membership proof -/
def kEquiv (n k : ℕ) : KSet n k ≃ lev (Fin (2 ^ n)) k :=
  Equiv.subtypeEquivRight fun S => by
    simp [groverTargetSets, Finset.mem_powersetCard]

/-- HY is invariant under reindexing -/
theorem HY_reindex {ι ι' : Type} [Fintype ι] [Fintype ι'] {d : ℕ} (e : ι ≃ ι')
    (Y : ι' → ι' → ℝ) (D : ι' → ℝ) (h : HY (d := d) Y D) :
    HY (d := d) (fun S S' => Y (e S) (e S')) (fun S => D (e S)) := by
  intro u
  have key : ∀ F : ι' → ι' → ℝ, ∑ T, ∑ T', F T T' = ∑ S, ∑ S', F (e S) (e S') := fun F =>
    (Equiv.sum_comp e (fun T => ∑ T', F T T')).symm.trans
      (Finset.sum_congr rfl fun S _ => (Equiv.sum_comp e (fun T' => F (e S) T')).symm)
  have h1 := h (fun T => u (e.symm T))
  rw [key] at h1
  rw [← Equiv.sum_comp e (fun T => nsq (u (e.symm T)))] at h1
  simpa only [Equiv.symm_apply_apply] using h1

/-- the find-all floor at m = 1: every circuit meeting the find-all spec for k targets
    has average cost at least F_L(2^n, k - 1) -/
theorem findAll_floor_FL {n k Q : ℕ} (hk : 1 ≤ k) (hN : 2 * k ≤ 2 ^ n)
    (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1))
    (hmeets : MeetsFindAllSpec k c) (bound : ℝ)
    (hbound : AvgOracleCostBound k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle 1 S))
        (fun S ↦ programOf c S) bound) :
    FL (2 ^ n) (k - 1) ≤ bound := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hk
  have hN' : 2 * (k' + 1) ≤ Fintype.card (Fin (2 ^ n)) := by
    rw [Fintype.card_fin]; exact hN
  have hkN : k' + 1 ≤ 2 ^ n := by omega
  have hcore := fa_floor_core (n := n) (k := k' + 1) (Q := Q) hk hkN c hmeets
    (fun S S' => Ypot (Fin (2 ^ n)) k' (kEquiv n (k' + 1) S) (kEquiv n (k' + 1) S'))
    (fun x => by
      have h := HY_reindex (d := 2 ^ Q) (kEquiv n (k' + 1)) _ _
        (Ypot_HY (Fin (2 ^ n)) k' hN' x (d := 2 ^ Q))
      exact h)
    (fun S => le_of_eq (Ypot_diag _ _ _))
    bound hbound
  have key : ∀ F : lev (Fin (2 ^ n)) (k' + 1) → lev (Fin (2 ^ n)) (k' + 1) → ℝ,
      ∑ S, ∑ S', F (kEquiv n (k' + 1) S) (kEquiv n (k' + 1) S') = ∑ T, ∑ T', F T T' :=
    fun F =>
      (Finset.sum_congr rfl fun S _ => Equiv.sum_comp (kEquiv n (k' + 1)) (fun T' => F _ T')).trans
        (Equiv.sum_comp (kEquiv n (k' + 1)) (fun T => ∑ T', F T T'))
  rw [key (Ypot (Fin (2 ^ n)) k'), Ypot_sum _ _ hN', Fintype.card_fin] at hcore
  have hpos : (0 : ℝ) < ((2 ^ n).choose (k' + 1) : ℕ) := by
    exact_mod_cast Nat.choose_pos hkN
  rw [Nat.add_sub_cancel]
  exact le_of_mul_le_mul_left hcore hpos

end GroverParallel

#print axioms GroverParallel.kEquiv
#print axioms GroverParallel.HY_reindex
#print axioms GroverParallel.findAll_floor_FL
