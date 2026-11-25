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
# Locality of the Grover marking oracle (`m = 1`)

For `r : QRegister ((n + 1) * 1) Q` and `O x := r.embedUnitary (groverParallelMarkingOracle 1 {x})`:
* `GroverLowerBound.oracle_apply_of_addr_ne`: `O x` fixes every amplitude whose address (the `n`
  address wires of the oracle register) is not `x`;
* `GroverLowerBound.oracle_sq_sum_le`: `∑ x, ‖O x v - v‖² ≤ 4 ‖v‖²`, in coordinates.
-/

open QuantumComputation.Specs Operator
open scoped Matrix

namespace GroverLowerBound

/-! ### Local arithmetic on `Fin (2 ^ (n + 1))` -/

/-- The marker table of `groverSetMarkingOracle {x}`. -/
def mark {n : ℕ} (x : Fin (2 ^ n)) : Fin (2 ^ n) → Fin (2 ^ 1) :=
  fun y => if y ∈ ({x} : Finset (Fin (2 ^ n))) then 1 else 0

lemma setMarking_eq {n : ℕ} (x : Fin (2 ^ n)) :
    groverSetMarkingOracle ({x} : Finset (Fin (2 ^ n))) =
      permutationUnitary (tableAddPerm (mark x)) := rfl

/-- Address (the `x` part) of a local `(n + 1)`-qubit basis index. -/
def laddr {n : ℕ} (l : Fin (2 ^ (n + 1))) : Fin (2 ^ n) := (splitBasisEquiv n 1 l).1

lemma split_tableAddPerm {m k : ℕ} (f : Fin (2 ^ m) → Fin (2 ^ k)) (l : Fin (2 ^ (m + k))) :
    splitBasisEquiv m k (tableAddPerm f l) =
      ((splitBasisEquiv m k l).1, (splitBasisEquiv m k l).2 + f (splitBasisEquiv m k l).1) := by
  simp only [tableAddPerm, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

lemma laddr_tableAddPerm {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ 1)) (l : Fin (2 ^ (n + 1))) :
    laddr (tableAddPerm f l) = laddr l := by
  unfold laddr
  rw [split_tableAddPerm]

lemma tableAddPerm_eq_self {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ 1)) (l : Fin (2 ^ (n + 1)))
    (h : f (laddr l) = 0) : tableAddPerm f l = l := by
  apply (splitBasisEquiv n 1).injective
  rw [split_tableAddPerm]
  have h' : f (splitBasisEquiv n 1 l).1 = 0 := h
  rw [h', add_zero]

/-- The inverse of the all-ones table permutation. -/
def cflip (n : ℕ) : Equiv.Perm (Fin (2 ^ (n + 1))) :=
  (tableAddPerm (fun _ : Fin (2 ^ n) => (1 : Fin (2 ^ 1))))⁻¹

lemma inv_apply_of_addr_ne {n : ℕ} (x : Fin (2 ^ n)) (l : Fin (2 ^ (n + 1)))
    (h : laddr l ≠ x) : (tableAddPerm (mark x))⁻¹ l = l := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  exact (tableAddPerm_eq_self _ _ (by simp [mark, h])).symm

lemma inv_apply_of_addr_eq {n : ℕ} (x : Fin (2 ^ n)) (l : Fin (2 ^ (n + 1)))
    (h : laddr l = x) : (tableAddPerm (mark x))⁻¹ l = cflip n l := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  have hm : tableAddPerm (fun _ : Fin (2 ^ n) => (1 : Fin (2 ^ 1))) (cflip n l) = l := by
    unfold cflip
    exact Equiv.apply_symm_apply _ _
  have haddr : laddr (cflip n l) = x := by
    rw [← laddr_tableAddPerm (fun _ : Fin (2 ^ n) => (1 : Fin (2 ^ 1))) (cflip n l), hm]
    exact h
  have key : tableAddPerm (mark x) (cflip n l) =
      tableAddPerm (fun _ : Fin (2 ^ n) => (1 : Fin (2 ^ 1))) (cflip n l) := by
    apply (splitBasisEquiv n 1).injective
    rw [split_tableAddPerm, split_tableAddPerm]
    have h1 : mark x (splitBasisEquiv n 1 (cflip n l)).1 = 1 := by
      have : (splitBasisEquiv n 1 (cflip n l)).1 = x := haddr
      rw [this]
      simp [mark]
    exact congrArg (fun y => ((splitBasisEquiv n 1 (cflip n l)).1,
      (splitBasisEquiv n 1 (cflip n l)).2 + y)) h1
  rw [key, hm]

/-! ### Embedding a permutation into a register -/

lemma perm_apply {k Q : ℕ} (R : QRegister k Q) (e : Equiv.Perm (Fin (2 ^ k)))
    (v : Fin (2 ^ Q) → ℂ) (i : Fin (2 ^ Q)) :
    ((R.embedMatrix ((e⁻¹).permMatrix ℂ)) *ᵥ v) i =
      v (R.replaceIndex i (e⁻¹ (R.extractIndex i))) := by
  rw [QRegister.embedMatrix_mulVec_apply]
  have : ∑ l, (e⁻¹).permMatrix ℂ (R.extractIndex i) l *
      v (R.basisSplitEquiv.symm (l, (R.basisSplitEquiv i).2)) =
      ((e⁻¹).permMatrix ℂ *ᵥ
        (fun l => v (R.basisSplitEquiv.symm (l, (R.basisSplitEquiv i).2)))) (R.extractIndex i) :=
    rfl
  rw [this, Matrix.permMatrix_mulVec]
  rfl

/-! ### The oracle for `m = 1` -/

lemma parallel_one {n : ℕ} (S : Finset (Fin (2 ^ n))) :
    groverParallelMarkingOracle 1 S =
      (QRegister.block 0 (n + 1) (by omega)).embedUnitary (groverSetMarkingOracle S) := by
  simp [groverParallelMarkingOracle, List.ofFn_succ]

/-- The `(n + 1)`-wire register of the oracle inside the machine: marker wire first, then the
`n` address wires. -/
def oreg {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) : QRegister (n + 1) Q :=
  r.compose (QRegister.block 0 (n + 1) (by omega))

lemma oracle_val {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) (x : Fin (2 ^ n)) :
    (r.embedUnitary (groverParallelMarkingOracle 1 {x})).1 =
      (oreg r).embedMatrix (((tableAddPerm (mark x))⁻¹).permMatrix ℂ) := by
  rw [parallel_one, ← QRegister.embedUnitary_compose]
  rfl

/-- The address (the `n` address wires, read as an index) of a basis index `i`. -/
def addr {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) (i : Fin (2 ^ Q)) : Fin (2 ^ n) :=
  (splitBasisEquiv n 1 ((r.compose (QRegister.block 0 (n + 1) (by omega))).extractIndex i)).1

lemma addr_eq {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) (i : Fin (2 ^ Q)) :
    addr r i = laddr ((oreg r).extractIndex i) := rfl

/-- Pointwise fact: `O x` fixes every amplitude whose address is not `x`. -/
theorem oracle_apply_of_addr_ne {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) (x : Fin (2 ^ n))
    (v : Fin (2 ^ Q) → ℂ) (i : Fin (2 ^ Q)) (h : addr r i ≠ x) :
    ((r.embedUnitary (groverParallelMarkingOracle 1 {x})).1 *ᵥ v) i = v i := by
  rw [oracle_val, perm_apply, inv_apply_of_addr_ne x _ (by rwa [← addr_eq])]
  exact congrArg v (QRegister.replaceIndex_extractIndex _ _)

/-! ### The squared-sum bound -/

/-- The flip of the marker wire, as a bijection of `Fin (2 ^ Q)`. -/
noncomputable def flipEquiv {n Q : ℕ} (R : QRegister (n + 1) Q) : Equiv.Perm (Fin (2 ^ Q)) :=
  R.basisSplitEquiv.trans
    ((Equiv.prodCongr (cflip n) (Equiv.refl _)).trans R.basisSplitEquiv.symm)

lemma flipEquiv_apply {n Q : ℕ} (R : QRegister (n + 1) Q) (i : Fin (2 ^ Q)) :
    flipEquiv R i = R.replaceIndex i (cflip n (R.extractIndex i)) := rfl

lemma normSq_sub_le (a b : ℂ) :
    Complex.normSq (a - b) ≤ 2 * Complex.normSq a + 2 * Complex.normSq b := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  nlinarith [sq_nonneg (a.re + b.re), sq_nonneg (a.im + b.im)]

lemma sum_x_le {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) (v : Fin (2 ^ Q) → ℂ)
    (i : Fin (2 ^ Q)) :
    ∑ x : Fin (2 ^ n),
        Complex.normSq (((r.embedUnitary (groverParallelMarkingOracle 1 {x})).1 *ᵥ v - v) i) ≤
      2 * Complex.normSq (v (flipEquiv (oreg r) i)) + 2 * Complex.normSq (v i) := by
  rw [Finset.sum_eq_single (addr r i)]
  · have h1 : ((r.embedUnitary (groverParallelMarkingOracle 1 {addr r i})).1 *ᵥ v) i =
        v (flipEquiv (oreg r) i) := by
      rw [oracle_val, perm_apply, inv_apply_of_addr_eq (addr r i) ((oreg r).extractIndex i) rfl,
        flipEquiv_apply]
    rw [Pi.sub_apply, h1]
    exact normSq_sub_le _ _
  · intro x _ hx
    rw [Pi.sub_apply, oracle_apply_of_addr_ne r x v i (Ne.symm hx), sub_self, map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Main theorem: the family `O x = r.embedUnitary (groverParallelMarkingOracle 1 {x})` satisfies
`∑ x, ‖O x v - v‖² ≤ 4 ‖v‖²`. -/
theorem oracle_sq_sum_le {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) (v : Fin (2 ^ Q) → ℂ) :
    ∑ x : Fin (2 ^ n), ∑ i,
        Complex.normSq (((r.embedUnitary (groverParallelMarkingOracle 1 {x})).1 *ᵥ v - v) i) ≤
      4 * ∑ i, Complex.normSq (v i) := by
  calc ∑ x : Fin (2 ^ n), ∑ i,
        Complex.normSq (((r.embedUnitary (groverParallelMarkingOracle 1 {x})).1 *ᵥ v - v) i)
      = ∑ i, ∑ x : Fin (2 ^ n),
        Complex.normSq (((r.embedUnitary (groverParallelMarkingOracle 1 {x})).1 *ᵥ v - v) i) :=
          Finset.sum_comm
    _ ≤ ∑ i, (2 * Complex.normSq (v (flipEquiv (oreg r) i)) + 2 * Complex.normSq (v i)) :=
          Finset.sum_le_sum fun i _ => sum_x_le r v i
    _ = 4 * ∑ i, Complex.normSq (v i) := by
          have h := Equiv.sum_comp (flipEquiv (oreg r)) (fun j => Complex.normSq (v j))
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h]
          ring

end GroverLowerBound

#print axioms GroverLowerBound.oracle_apply_of_addr_ne
#print axioms GroverLowerBound.oracle_sq_sum_le
