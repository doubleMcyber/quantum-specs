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
import LowerBounds.Grover.FindAllOracle
import LowerBounds.Grover.ParallelOracle
import LowerBounds.Grover.ParallelLink
import Mathlib

/-!
# The oracle hypothesis with `m` slots

`hH_tel`: under `HY Y (signX x)` for every address `x`, a call to Google's marking oracle with `m`
slots lowers `gramY Y` by at most `m` times the total squared norm, by splitting the call into its
slots. `hH_multi_scaled` restates this for the potential `Y / m`, in the form that `pwY_ens_mono`
needs.
-/

open QuantumComputation.Specs Operator GroverLowerBound
open scoped Matrix

namespace GroverParallel

/-! ### Helpers on the set-marking oracle -/

private abbrev mkT {n : ℕ} (S : Finset (Fin (2 ^ n))) : Fin (2 ^ n) → Fin (2 ^ 1) :=
  fun x => if x ∈ S then (1 : Fin (2 ^ 1)) else 0

private lemma setMarking_val' {n : ℕ} (S : Finset (Fin (2 ^ n))) :
    (groverSetMarkingOracle S).1 = ((tableAddPerm (mkT S))⁻¹).permMatrix ℂ := rfl

private lemma fin_two_double' : ∀ c : Fin (2 ^ 1), c + c = 0 := by
  decide

private lemma tab_invol' {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ 1)) (l : Fin (2 ^ (n + 1))) :
    tableAddPerm f (tableAddPerm f l) = l := by
  apply (splitBasisEquiv n 1).injective
  rw [GroverLowerBound.split_tableAddPerm, GroverLowerBound.split_tableAddPerm]
  refine Prod.ext rfl ?_
  dsimp only
  rw [add_assoc, fin_two_double', add_zero]

private lemma tab_inv_eq' {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ 1)) :
    (tableAddPerm f)⁻¹ = tableAddPerm f :=
  Equiv.ext fun l => Equiv.Perm.inv_eq_iff_eq.mpr (tab_invol' f l).symm

private lemma setMarking_sa' {n : ℕ} (S : Finset (Fin (2 ^ n))) :
    ((groverSetMarkingOracle S).1).conjTranspose = (groverSetMarkingOracle S).1 := by
  rw [setMarking_val', Matrix.conjTranspose_permMatrix, inv_inv, tab_inv_eq']

private lemma laddr_cflip' {n : ℕ} (y : Fin (2 ^ (n + 1))) : laddr (cflip n y) = laddr y := by
  have hm : tableAddPerm (fun _ : Fin (2 ^ n) => (1 : Fin (2 ^ 1))) (cflip n y) = y := by
    unfold cflip
    exact Equiv.apply_symm_apply _ _
  have h := laddr_tableAddPerm (fun _ : Fin (2 ^ n) => (1 : Fin (2 ^ 1))) (cflip n y)
  rw [hm] at h
  exact h.symm

private lemma inv_apply_one' {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ 1)) (l : Fin (2 ^ (n + 1)))
    (h : f (laddr l) = 1) : (tableAddPerm f)⁻¹ l = cflip n l := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  have hm : tableAddPerm (fun _ : Fin (2 ^ n) => (1 : Fin (2 ^ 1))) (cflip n l) = l := by
    unfold cflip
    exact Equiv.apply_symm_apply _ _
  have haddr : laddr (cflip n l) = laddr l := laddr_cflip' l
  have key : tableAddPerm f (cflip n l) =
      tableAddPerm (fun _ : Fin (2 ^ n) => (1 : Fin (2 ^ 1))) (cflip n l) := by
    apply (splitBasisEquiv n 1).injective
    rw [split_tableAddPerm, split_tableAddPerm]
    have h1 : f (splitBasisEquiv n 1 (cflip n l)).1 = 1 := by
      have h2 : (splitBasisEquiv n 1 (cflip n l)).1 = laddr l := haddr
      rw [h2]
      exact h
    exact congrArg (fun y => ((splitBasisEquiv n 1 (cflip n l)).1,
      (splitBasisEquiv n 1 (cflip n l)).2 + y)) h1
  exact (key.trans hm).symm

private lemma inv_apply_zero' {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ 1)) (l : Fin (2 ^ (n + 1)))
    (h : f (laddr l) = 0) : (tableAddPerm f)⁻¹ l = l := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  exact (tableAddPerm_eq_self f l h).symm

private lemma slot_apply {n Q : ℕ} (R : QRegister (n + 1) Q) (S : Finset (Fin (2 ^ n)))
    (w : Fin (2 ^ Q) → ℂ) (l : Fin (2 ^ Q)) :
    (R.embedMatrix (groverSetMarkingOracle S).1 *ᵥ w) l =
      if laddr (R.extractIndex l) ∈ S then w (GroverLowerBound.flipEquiv R l) else w l := by
  rw [setMarking_val', GroverLowerBound.perm_apply]
  by_cases h : laddr (R.extractIndex l) ∈ S
  · have hf : mkT S (laddr (R.extractIndex l)) = 1 := if_pos h
    rw [if_pos h, inv_apply_one' _ _ hf, GroverLowerBound.flipEquiv_apply]
  · have hf : mkT S (laddr (R.extractIndex l)) = 0 := if_neg h
    rw [if_neg h, inv_apply_zero' _ _ hf]
    exact congrArg w (QRegister.replaceIndex_extractIndex _ _)

private lemma addr_flip' {n Q : ℕ} (R : QRegister (n + 1) Q) (l : Fin (2 ^ Q)) :
    laddr (R.extractIndex (GroverLowerBound.flipEquiv R l)) = laddr (R.extractIndex l) := by
  rw [GroverLowerBound.flipEquiv_apply, QRegister.extractIndex_replaceIndex]
  exact laddr_cflip' _

private lemma mulVec_single_apply'' {d : Type*} [Fintype d] [DecidableEq d]
    (M : Matrix d d ℂ) (j l : d) : (M *ᵥ Pi.single j (1 : ℂ)) l = M l j := by
  rw [Matrix.mulVec_single_one]
  rfl

private lemma matrix_ext_mulVec' {d : ℕ} (M N : Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ w, M *ᵥ w = N *ᵥ w) : M = N := by
  ext l j
  have h1 := congrFun (h (Pi.single j 1)) l
  rw [mulVec_single_apply'', mulVec_single_apply''] at h1
  exact h1

/-! ### The reflection data of one slot -/

/-- The diagonal projector onto the basis states of address `x`. -/
private noncomputable def slotE {n Q : ℕ} (R : QRegister (n + 1) Q) (x : Fin (2 ^ n)) :
    Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ :=
  Matrix.diagonal fun l => if laddr (R.extractIndex l) = x then (1 : ℂ) else 0

/-- The all-addresses oracle on the slot. -/
private noncomputable def slotF {n Q : ℕ} (R : QRegister (n + 1) Q) :
    Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ :=
  R.embedMatrix (groverSetMarkingOracle (Finset.univ : Finset (Fin (2 ^ n)))).1

private lemma slotE_apply {n Q : ℕ} (R : QRegister (n + 1) Q) (x : Fin (2 ^ n))
    (w : Fin (2 ^ Q) → ℂ) (l : Fin (2 ^ Q)) :
    (slotE R x *ᵥ w) l = if laddr (R.extractIndex l) = x then w l else 0 := by
  unfold slotE
  rw [Matrix.mulVec_diagonal]
  split_ifs <;> simp

private lemma slotF_apply {n Q : ℕ} (R : QRegister (n + 1) Q) (w : Fin (2 ^ Q) → ℂ)
    (l : Fin (2 ^ Q)) : (slotF R *ᵥ w) l = w (GroverLowerBound.flipEquiv R l) := by
  unfold slotF
  rw [slot_apply, if_pos (Finset.mem_univ _)]

private lemma slotE_sa {n Q : ℕ} (R : QRegister (n + 1) Q) (x : Fin (2 ^ n)) :
    (slotE R x)ᴴ = slotE R x := by
  unfold slotE
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext l
  by_cases h : laddr (R.extractIndex l) = x <;> simp [h]

private lemma slotE_id {n Q : ℕ} (R : QRegister (n + 1) Q) (x : Fin (2 ^ n)) :
    slotE R x * slotE R x = slotE R x := by
  unfold slotE
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext l
  split_ifs <;> simp

private lemma slotE_orth {n Q : ℕ} (R : QRegister (n + 1) Q) (x y : Fin (2 ^ n))
    (hxy : x ≠ y) : slotE R x * slotE R y = 0 := by
  unfold slotE
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
  congr 1
  funext l
  by_cases h : laddr (R.extractIndex l) = x
  · have h2 : ¬ laddr (R.extractIndex l) = y := fun h2 => hxy (h.symm.trans h2)
    simp [h, h2, hxy]
  · simp [h]

private lemma slotF_sa {n Q : ℕ} (R : QRegister (n + 1) Q) : (slotF R)ᴴ = slotF R := by
  unfold slotF
  rw [← QRegister.embedMatrix_conjTranspose, setMarking_sa']

private lemma slotF_inv {n Q : ℕ} (R : QRegister (n + 1) Q) : slotF R * slotF R = 1 := by
  have h : (slotF R)ᴴ * slotF R = 1 :=
    Unitary.star_mul_self_of_mem
      (R.embedUnitary (groverSetMarkingOracle (Finset.univ : Finset (Fin (2 ^ n))))).2
  rw [slotF_sa] at h
  exact h

private lemma slotF_comm {n Q : ℕ} (R : QRegister (n + 1) Q) (x : Fin (2 ^ n)) :
    slotF R * slotE R x = slotE R x * slotF R := by
  apply matrix_ext_mulVec'
  intro w
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  funext l
  simp only [slotF_apply, slotE_apply, addr_flip']

private lemma slot_proj_apply {n Q : ℕ} (R : QRegister (n + 1) Q) (x : Fin (2 ^ n))
    (w : Fin (2 ^ Q) → ℂ) (l : Fin (2 ^ Q)) :
    (reflProj (slotE R) (slotF R) x *ᵥ w) l =
      if laddr (R.extractIndex l) = x then (1 / 2 : ℂ) * (w l - w (GroverLowerBound.flipEquiv R l)) else 0 := by
  have h : reflProj (slotE R) (slotF R) x *ᵥ w =
      (1 / 2 : ℂ) • (slotE R x *ᵥ w - slotE R x *ᵥ (slotF R *ᵥ w)) := by
    unfold reflProj
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.mulVec_mulVec]
  rw [h, Pi.smul_apply, Pi.sub_apply, slotE_apply, slotE_apply, slotF_apply, smul_eq_mul]
  by_cases hx : laddr (R.extractIndex l) = x
  · simp [hx]
  · simp [hx]

private lemma slot_eq_refl {n k Q : ℕ} (R : QRegister (n + 1) Q) (S : KSet n k) :
    R.embedMatrix (groverSetMarkingOracle S.1).1 =
      1 + ∑ x, (((signX x S : ℝ) : ℂ) - 1) • reflProj (slotE R) (slotF R) x := by
  apply matrix_ext_mulVec'
  intro w
  funext l
  have hL : (R.embedMatrix (groverSetMarkingOracle S.1).1 *ᵥ w) l =
      if laddr (R.extractIndex l) ∈ S.1 then w (GroverLowerBound.flipEquiv R l) else w l :=
    slot_apply R S.1 w l
  rw [hL]
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec,
    Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, slot_proj_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases h : laddr (R.extractIndex l) ∈ S.1
  · simp only [signX, if_pos h]
    push_cast
    ring
  · simp only [signX, if_neg h]
    push_cast
    ring

/-- one slot: a set-marking oracle on any `(n + 1)`-wire register -/
theorem hH_slot {n k Q : ℕ} (Y : KSet n k → KSet n k → ℝ)
    (hY : ∀ x : Fin (2 ^ n), HY (d := 2 ^ Q) Y (signX x))
    (R : QRegister (n + 1) Q) (v : KSet n k → Fin (2 ^ Q) → ℂ) :
    gramY Y v - gramY Y (fun S => R.embedMatrix (groverSetMarkingOracle S.1).1 *ᵥ v S)
      ≤ ∑ S, nsq (v S) :=
  hH_of_refl Y (fun S => R.embedMatrix (groverSetMarkingOracle S.1).1) (slotE R) (slotF R)
    (fun x S => signX x S)
    (slotE_sa R) (slotE_id R) (slotE_orth R) (slotF_sa R) (slotF_inv R) (slotF_comm R)
    (fun S => slot_eq_refl R S) hY v

/-! ### Telescoping over the slots -/

/-- The `(n + 1)`-wire register of slot `i` inside the oracle register `r`. -/
private abbrev slotReg' {n m Q : ℕ} (r : QRegister ((n + 1) * m) Q) (i : Fin m) :
    QRegister (n + 1) Q :=
  r.compose (QRegister.block (i.val * (n + 1)) (n + 1) (by nlinarith [i.isLt]))

private lemma embed_list_prod' {k Q : ℕ} (r : QRegister k Q) (l : List (Unitary (2 ^ k))) :
    (r.embedUnitary l.prod).1 = (l.map fun U => r.embedMatrix U.1).prod := by
  induction l with
  | nil =>
    rw [List.prod_nil, QRegister.embedUnitary_one, List.map_nil, List.prod_nil]
    rfl
  | cons U t ih =>
    rw [List.prod_cons, QRegister.embedUnitary_mul, List.map_cons, List.prod_cons, ← ih]
    rfl

private lemma oracle_val_list' {n m Q : ℕ} (r : QRegister ((n + 1) * m) Q)
    (S : Finset (Fin (2 ^ n))) :
    (r.embedUnitary (groverParallelMarkingOracle m S)).1 =
      (List.ofFn fun i : Fin m => (slotReg' r i).embedMatrix (groverSetMarkingOracle S).1).prod := by
  unfold groverParallelMarkingOracle
  rw [embed_list_prod', List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
  exact (congrArg Subtype.val (QRegister.embedUnitary_compose r
    (QRegister.block (i.val * (n + 1)) (n + 1) (by nlinarith [i.isLt]))
    (groverSetMarkingOracle S))).symm

/-- the product of the slot embeddings of a list of registers -/
private noncomputable def slotProd {n Q : ℕ} (Rs : List (QRegister (n + 1) Q))
    (S : Finset (Fin (2 ^ n))) : Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ :=
  (Rs.map fun R => R.embedMatrix (groverSetMarkingOracle S).1).prod

private lemma slotProd_nsq {n Q : ℕ} (S : Finset (Fin (2 ^ n))) (Rs : List (QRegister (n + 1) Q))
    (w : Fin (2 ^ Q) → ℂ) : nsq (slotProd Rs S *ᵥ w) = nsq w := by
  induction Rs generalizing w with
  | nil =>
    simp [slotProd]
  | cons R t ih =>
    have h : slotProd (R :: t) S *ᵥ w =
        (R.embedUnitary (groverSetMarkingOracle S)).1 *ᵥ (slotProd t S *ᵥ w) := by
      unfold slotProd
      rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec]
      rfl
    rw [h, GroverLowerBound.nsq_unit, ih]

private lemma gram_tel {n k Q : ℕ} (Y : KSet n k → KSet n k → ℝ)
    (hY : ∀ x : Fin (2 ^ n), HY (d := 2 ^ Q) Y (signX x))
    (Rs : List (QRegister (n + 1) Q)) (v : KSet n k → Fin (2 ^ Q) → ℂ) :
    gramY Y v - gramY Y (fun S => slotProd Rs S.1 *ᵥ v S) ≤ (Rs.length : ℝ) * ∑ S, nsq (v S) := by
  induction Rs with
  | nil =>
    have h : (fun S : KSet n k => slotProd ([] : List (QRegister (n + 1) Q)) S.1 *ᵥ v S) = v := by
      funext S
      simp [slotProd]
    rw [h]
    simp
  | cons R t ih =>
    have h : (fun S : KSet n k => slotProd (R :: t) S.1 *ᵥ v S) =
        fun S => R.embedMatrix (groverSetMarkingOracle S.1).1 *ᵥ (slotProd t S.1 *ᵥ v S) := by
      funext S
      unfold slotProd
      rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec]
    rw [h]
    have h1 := hH_slot Y hY R (fun S => slotProd t S.1 *ᵥ v S)
    have h2 : ∑ S, nsq (slotProd t S.1 *ᵥ v S) = ∑ S, nsq (v S) :=
      Finset.sum_congr rfl fun S _ => slotProd_nsq S.1 t (v S)
    rw [h2] at h1
    rw [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

/-- m slots: the drop is at most `m` times the mass -/
theorem hH_tel {n m k Q : ℕ} (Y : KSet n k → KSet n k → ℝ)
    (hY : ∀ x : Fin (2 ^ n), HY (d := 2 ^ Q) Y (signX x))
    (c : ℕ) (r : QRegister ((n + 1) * m) Q) (v : KSet n k → Fin (2 ^ Q) → ℂ) :
    gramY Y v - gramY Y (fun S => GK n m k Q S c r *ᵥ v S) ≤ (m : ℝ) * ∑ S, nsq (v S) := by
  have hG : ∀ S : KSet n k, GK n m k Q S c r = slotProd (List.ofFn (slotReg' r)) S.1 := by
    intro S
    show (r.embedUnitary (groverParallelMarkingOracle m S.1)).1 = _
    rw [oracle_val_list']
    unfold slotProd
    rw [List.map_ofFn]
    rfl
  have h := gram_tel Y hY (List.ofFn (slotReg' r)) v
  rw [List.length_ofFn] at h
  simp only [← hG] at h
  exact h

private lemma gramY_div {ι : Type} [Fintype ι] {Q : ℕ} (Y : ι → ι → ℝ) (a : ℝ)
    (v : ι → Fin (2 ^ Q) → ℂ) : gramY (fun S S' => Y S S' / a) v = gramY Y v / a := by
  simp only [gramY, div_mul_eq_mul_div, Finset.sum_div]

/-- the scaled potential has exactly the `hH` shape of `pwY_ens_mono` -/
theorem hH_multi_scaled {n m k Q : ℕ} (hm : 1 ≤ m) (Y : KSet n k → KSet n k → ℝ)
    (hY : ∀ x : Fin (2 ^ n), HY (d := 2 ^ Q) Y (signX x))
    (c : ℕ) (r : QRegister ((n + 1) * m) Q) (v : KSet n k → Fin (2 ^ Q) → ℂ) :
    gramY (fun S S' => Y S S' / m) v - gramY (fun S S' => Y S S' / m) (fun S => GK n m k Q S c r *ᵥ v S)
      ≤ ∑ S, nsq (v S) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have h := hH_tel Y hY c r v
  rw [gramY_div, gramY_div, ← sub_div, div_le_iff₀ hmpos]
  linarith

end GroverParallel

#print axioms GroverParallel.hH_slot
#print axioms GroverParallel.hH_tel
#print axioms GroverParallel.hH_multi_scaled
