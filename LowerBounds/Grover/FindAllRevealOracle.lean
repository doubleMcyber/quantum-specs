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
import LowerBounds.Grover.ParallelOracle
import LowerBounds.Grover.ParallelLink
import Mathlib

/-!
# Google's marking oracle on one added target

`parallelOracle_insert`: for `x ∉ K`, the embedded oracle for `insert x K` is the oracle for `K`
times the oracle for `{x}`. `parallelOracle_single_sq_sum_le`: the single-target oracles move a
vector by a total squared amount of at most `4 m ‖u‖²`.
-/

open QuantumComputation.Specs Operator
open scoped Matrix
open GroverLowerBound (nsq)

namespace GroverParallel

/-! ### One slot -/

private abbrev dTab {n : ℕ} (S : Finset (Fin (2 ^ n))) : Fin (2 ^ n) → Fin (2 ^ 1) :=
  fun x => if x ∈ S then (1 : Fin (2 ^ 1)) else 0

private lemma dSetMarking_val {n : ℕ} (S : Finset (Fin (2 ^ n))) :
    (groverSetMarkingOracle S).1 = ((tableAddPerm (dTab S))⁻¹).permMatrix ℂ := rfl

private lemma dTab_insert {n : ℕ} (K : Finset (Fin (2 ^ n))) (x : Fin (2 ^ n)) (hx : x ∉ K) :
    dTab (insert x K) = dTab K + dTab {x} := by
  funext y
  by_cases h : y = x
  · subst h
    simp [dTab, hx]
  · simp [dTab, h]

private lemma dTab_add {n : ℕ} (f g : Fin (2 ^ n) → Fin (2 ^ 1)) :
    tableAddPerm (f + g) = tableAddPerm f * tableAddPerm g := by
  refine Equiv.ext fun l => ?_
  apply (splitBasisEquiv n 1).injective
  simp only [Equiv.Perm.mul_apply, GroverLowerBound.split_tableAddPerm]
  refine Prod.ext rfl ?_
  dsimp only
  simp only [Pi.add_apply]
  abel

private lemma dSetMarking_insert {n : ℕ} (K : Finset (Fin (2 ^ n))) (x : Fin (2 ^ n))
    (hx : x ∉ K) :
    (groverSetMarkingOracle (insert x K)).1 =
      (groverSetMarkingOracle K).1 * (groverSetMarkingOracle {x}).1 := by
  rw [dSetMarking_val, dSetMarking_val, dSetMarking_val, dTab_insert K x hx, dTab_add,
    mul_inv_rev, Matrix.permMatrix_mul]

/-! ### Slots -/

private abbrev dSlotReg {n m Q : ℕ} (r : QRegister ((n + 1) * m) Q) (i : Fin m) :
    QRegister (n + 1) Q :=
  r.compose (QRegister.block (i.val * (n + 1)) (n + 1) (by nlinarith [i.isLt]))

private lemma dSlot_disjoint {n m Q : ℕ} (r : QRegister ((n + 1) * m) Q) {i j : Fin m}
    (hij : i < j) : (dSlotReg r i).DisjointWires (dSlotReg r j) := by
  have hij' : i.val < j.val := hij
  have h : (i.val + 1) * (n + 1) ≤ j.val * (n + 1) :=
    Nat.mul_le_mul_right (n + 1) (Nat.succ_le_of_lt hij')
  exact QRegister.slice_disjoint_of_le r (i.val * (n + 1)) (n + 1) (j.val * (n + 1)) (n + 1)
    (by nlinarith [i.isLt]) (by nlinarith [j.isLt]) (by nlinarith [h])

private lemma dEmbed_list_prod {k Q : ℕ} (r : QRegister k Q) (l : List (Unitary (2 ^ k))) :
    (r.embedUnitary l.prod).1 = (l.map fun U => r.embedMatrix U.1).prod := by
  induction l with
  | nil =>
    rw [List.prod_nil, QRegister.embedUnitary_one, List.map_nil, List.prod_nil]
    rfl
  | cons U t ih =>
    rw [List.prod_cons, QRegister.embedUnitary_mul, List.map_cons, List.prod_cons, ← ih]
    rfl

private lemma dOracle_val_list {n m Q : ℕ} (r : QRegister ((n + 1) * m) Q)
    (S : Finset (Fin (2 ^ n))) :
    (r.embedUnitary (groverParallelMarkingOracle m S)).1 =
      (List.ofFn fun i : Fin m => (dSlotReg r i).embedMatrix (groverSetMarkingOracle S).1).prod := by
  unfold groverParallelMarkingOracle
  rw [dEmbed_list_prod, List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
  exact (congrArg Subtype.val (QRegister.embedUnitary_compose r
    (QRegister.block (i.val * (n + 1)) (n + 1) (by nlinarith [i.isLt]))
    (groverSetMarkingOracle S))).symm

/-! ### Splitting a product of slot factors -/

private lemma dOfFn_prod_mul {d : Type*} [Fintype d] [DecidableEq d] (m : ℕ) :
    ∀ (B C : Fin m → Matrix d d ℂ), (∀ i j, i ≠ j → Commute (C i) (B j)) →
      (List.ofFn fun i => B i * C i).prod = (List.ofFn B).prod * (List.ofFn C).prod := by
  induction m with
  | zero =>
    intro B C _
    simp
  | succ m ih =>
    intro B C h
    have e1 : (List.ofFn fun i => B i * C i) =
        (B 0 * C 0) :: List.ofFn fun i : Fin m => B i.succ * C i.succ := List.ofFn_succ
    have e2 : List.ofFn B = B 0 :: List.ofFn fun i : Fin m => B i.succ := List.ofFn_succ
    have e3 : List.ofFn C = C 0 :: List.ofFn fun i : Fin m => C i.succ := List.ofFn_succ
    rw [e1, e2, e3, List.prod_cons, List.prod_cons,
      List.prod_cons,
      ih (fun i => B i.succ) (fun i => C i.succ)
        (fun i j hij => h i.succ j.succ (fun e => hij (Fin.succ_injective _ e)))]
    have hc : Commute (C 0) (List.ofFn fun i : Fin m => B i.succ).prod := by
      refine Commute.list_prod_right _ _ ?_
      intro b hb
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
      exact h 0 j.succ (Fin.succ_ne_zero j).symm
    have hc' : C 0 * (List.ofFn fun i : Fin m => B i.succ).prod =
        (List.ofFn fun i : Fin m => B i.succ).prod * C 0 := hc
    calc B 0 * C 0 * ((List.ofFn fun i : Fin m => B i.succ).prod *
          (List.ofFn fun i : Fin m => C i.succ).prod)
        = B 0 * (C 0 * (List.ofFn fun i : Fin m => B i.succ).prod) *
            (List.ofFn fun i : Fin m => C i.succ).prod := by simp only [Matrix.mul_assoc]
      _ = B 0 * ((List.ofFn fun i : Fin m => B i.succ).prod * C 0) *
            (List.ofFn fun i : Fin m => C i.succ).prod := by rw [hc']
      _ = B 0 * (List.ofFn fun i : Fin m => B i.succ).prod *
            (C 0 * (List.ofFn fun i : Fin m => C i.succ).prod) := by simp only [Matrix.mul_assoc]

/-! ### The deliverables -/

/-- for x ∉ K the m-slot marking oracle of K ∪ {x} is that of K times that of {x} -/
theorem parallelOracle_insert {n m Q : ℕ} (r : QRegister ((n + 1) * m) Q)
    (K : Finset (Fin (2 ^ n))) (x : Fin (2 ^ n)) (hx : x ∉ K) :
    (r.embedUnitary (groverParallelMarkingOracle m (insert x K))).1 =
      (r.embedUnitary (groverParallelMarkingOracle m K)).1 *
        (r.embedUnitary (groverParallelMarkingOracle m {x})).1 := by
  rw [dOracle_val_list, dOracle_val_list, dOracle_val_list]
  have hslot : ∀ i : Fin m,
      (dSlotReg r i).embedMatrix (groverSetMarkingOracle (insert x K)).1 =
        (dSlotReg r i).embedMatrix (groverSetMarkingOracle K).1 *
          (dSlotReg r i).embedMatrix (groverSetMarkingOracle {x}).1 := fun i => by
    rw [dSetMarking_insert K x hx, QRegister.embedMatrix_mul]
  simp only [hslot]
  refine dOfFn_prod_mul m
    (fun i => (dSlotReg r i).embedMatrix (groverSetMarkingOracle K).1)
    (fun i => (dSlotReg r i).embedMatrix (groverSetMarkingOracle {x}).1) ?_
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact QRegister.embedMatrix_comm_of_disjoint _ _ (dSlot_disjoint r h) _ _
  · exact (QRegister.embedMatrix_comm_of_disjoint _ _ (dSlot_disjoint r h) _ _).symm

/-- the single-target footprints add up to at most m -/
theorem parallelOracle_single_sq_sum_le {n m Q : ℕ} (r : QRegister ((n + 1) * m) Q)
    (u : Fin (2 ^ Q) → ℂ) :
    ∑ x : Fin (2 ^ n), nsq ((r.embedUnitary (groverParallelMarkingOracle m {x})).1 *ᵥ u - u) ≤
      4 * (m : ℝ) * nsq u := by
  have h := parallelOracle_sq_sum_le 1 le_rfl r u
  rw [groverTargetSets, Finset.powersetCard_one, Finset.sum_map] at h
  refine le_trans h (le_of_eq ?_)
  rw [Nat.choose_zero_right]
  simp

end GroverParallel

#print axioms GroverParallel.parallelOracle_insert
#print axioms GroverParallel.parallelOracle_single_sq_sum_le
