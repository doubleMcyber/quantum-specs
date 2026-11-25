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
import QuantumComputationSpecs.Algorithms.Grover
import Mathlib

/-!
# Averaging over revealed targets

`sum_reveal` counts each `k`-set `S` once for each of its `k` elements `x`, as `insert x K` with
`K = S \ {x}`. `exists_reveal_le`: for every function `f` on `k`-sets there is a `(k - 1)`-set `K`
whose average of `f (insert x K)` over `x ∉ K` is at most the average of `f` over all `k`-sets.
-/

open QuantumComputation.Specs

namespace GroverParallel

/-- double counting: pairs (K, x) with |K| = k - 1, x ∉ K are pairs (S, x) with |S| = k, x ∈ S -/
theorem sum_reveal {n k : ℕ} (hk : 1 ≤ k) (f : Finset (Fin (2 ^ n)) → ℝ) :
    ∑ K ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard (k - 1),
        ∑ x ∈ Finset.univ.filter (fun x => x ∉ K), f (insert x K) =
      (k : ℝ) * ∑ S ∈ groverTargetSets n k, f S := by
  classical
  have hR : (k : ℝ) * ∑ S ∈ groverTargetSets n k, f S =
      ∑ S ∈ groverTargetSets n k, ∑ _x ∈ S, f S := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun S hS => ?_)
    have hc : S.card = k := by
      unfold groverTargetSets at hS
      exact (Finset.mem_powersetCard.mp hS).2
    rw [Finset.sum_const, hc, nsmul_eq_mul]
  rw [hR, Finset.sum_sigma' ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard (k - 1))
      (fun K => Finset.univ.filter (fun x => x ∉ K)) (fun K x => f (insert x K)),
    Finset.sum_sigma' (groverTargetSets n k) (fun S => S) (fun S _ => f S)]
  refine Finset.sum_bij' (fun p _ => (⟨insert p.2 p.1, p.2⟩ : Σ _ : Finset (Fin (2 ^ n)), Fin (2 ^ n)))
    (fun q _ => (⟨q.1.erase q.2, q.2⟩ : Σ _ : Finset (Fin (2 ^ n)), Fin (2 ^ n)))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨K, x⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.subset_univ] at hp
    simp only [groverTargetSets, Finset.mem_sigma, Finset.mem_powersetCard, Finset.subset_univ,
      true_and, Finset.mem_insert, true_or, and_true]
    rw [Finset.card_insert_of_notMem hp.2, hp.1]
    omega
  · rintro ⟨S, x⟩ hq
    simp only [groverTargetSets, Finset.mem_sigma, Finset.mem_powersetCard, Finset.subset_univ,
      true_and] at hq
    simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Finset.mem_filter, Finset.mem_univ, Finset.notMem_erase, not_false_eq_true, and_true]
    rw [Finset.card_erase_of_mem hq.2, hq.1]
  · rintro ⟨K, x⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp [Finset.erase_insert hp.2]
  · rintro ⟨S, x⟩ hq
    simp only [Finset.mem_sigma] at hq
    simp [Finset.insert_erase hq.2]
  · rintro ⟨K, x⟩ _
    rfl

/-- some revealed set has average at most the overall average -/
theorem exists_reveal_le {n k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ 2 ^ n) (f : Finset (Fin (2 ^ n)) → ℝ) :
    ∃ K : Finset (Fin (2 ^ n)), K.card = k - 1 ∧
      (∑ x ∈ Finset.univ.filter (fun x => x ∉ K), f (insert x K)) / ((2 ^ n - (k - 1) : ℕ) : ℝ) ≤
        (∑ S ∈ groverTargetSets n k, f S) / ((groverTargetSets n k).card : ℝ) := by
  classical
  set P : Finset (Finset (Fin (2 ^ n))) := (Finset.univ : Finset (Fin (2 ^ n))).powersetCard (k - 1)
    with hP
  set c : ℝ := ((2 ^ n - (k - 1) : ℕ) : ℝ) with hc
  set T : ℝ := ∑ S ∈ groverTargetSets n k, f S with hT
  have hN : (Fintype.card (Fin (2 ^ n))) = 2 ^ n := by simp
  have hPcard : P.card = (2 ^ n).choose (k - 1) := by
    rw [hP, Finset.card_powersetCard, Finset.card_univ, hN]
  have hGcard : (groverTargetSets n k).card = (2 ^ n).choose k := by
    unfold groverTargetSets
    rw [Finset.card_powersetCard, Finset.card_univ, hN]
  have hcpos : 0 < c := by
    rw [hc]; exact_mod_cast (by omega : 0 < 2 ^ n - (k - 1))
  have hGpos : (0 : ℝ) < ((2 ^ n).choose k : ℕ) := by
    exact_mod_cast Nat.choose_pos hkN
  have hPne : P.Nonempty := by
    rw [← Finset.card_pos, hPcard]
    exact Nat.choose_pos (by omega)
  -- the counting identity C(N, k-1) * (N - (k-1)) = k * C(N, k)
  have hid : ((2 ^ n).choose (k - 1) : ℝ) * c = (k : ℝ) * ((2 ^ n).choose k : ℝ) := by
    have h := Nat.choose_succ_right_eq (2 ^ n) (k - 1)
    have hk' : k - 1 + 1 = k := by omega
    rw [hk'] at h
    rw [hc]
    exact_mod_cast (by rw [mul_comm k]; exact h.symm :
      (2 ^ n).choose (k - 1) * (2 ^ n - (k - 1)) = k * (2 ^ n).choose k)
  have hsum : ∑ K ∈ P, ∑ x ∈ Finset.univ.filter (fun x => x ∉ K), f (insert x K) = (k : ℝ) * T :=
    sum_reveal hk f
  rw [hGcard]
  by_contra hcon
  have hlt : ∀ K ∈ P, T / ((2 ^ n).choose k : ℝ) <
      (∑ x ∈ Finset.univ.filter (fun x => x ∉ K), f (insert x K)) / c := by
    intro K hK
    have hKc : K.card = k - 1 := (Finset.mem_powersetCard.mp hK).2
    by_contra h
    exact hcon ⟨K, hKc, not_lt.mp h⟩
  have h1 := Finset.sum_lt_sum_of_nonempty hPne hlt
  rw [Finset.sum_const, nsmul_eq_mul, hPcard, ← Finset.sum_div, hsum] at h1
  -- h1 : C(N,k-1) * (T / C(N,k)) < k * T / c
  have hC1 : ((2 ^ n).choose (k - 1) : ℝ) = (k : ℝ) * ((2 ^ n).choose k : ℝ) / c := by
    rw [eq_div_iff hcpos.ne']; exact hid
  have h2 : ((2 ^ n).choose (k - 1) : ℝ) * (T / ((2 ^ n).choose k : ℝ)) = (k : ℝ) * T / c := by
    rw [hC1]
    field_simp
  linarith

end GroverParallel

#print axioms GroverParallel.sum_reveal
#print axioms GroverParallel.exists_reveal_le
