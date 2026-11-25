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
import LowerBounds.Grover.OracleLocality
import LowerBounds.Grover.Hybrid
import Mathlib

/-!
# The parallel marking oracle (`m` slots, `k` marked items)

For `r : QRegister ((n + 1) * m) Q` and `O S := r.embedUnitary (groverParallelMarkingOracle m S)`:
* `parallelOracle_selfAdjoint`, `parallelOracle_mul_self`: `O S` is a self-adjoint involution
  (a product of pairwise commuting slot embeddings of the self-adjoint permutation matrix of
  `groverSetMarkingOracle S`);
* `card_targetSets_mem`, `choose_mul_two_pow`: counting facts for `groverTargetSets n k`;
* `parallelOracle_sq_sum_le`: `∑_S ‖O S v - v‖² ≤ 4 m C(2^n - 1, k - 1) ‖v‖²`, by a union bound on
  the set of basis states at which some slot address lies in `S`.
-/

open QuantumComputation.Specs Operator
open scoped Matrix
open GroverLowerBound (nsq)

namespace GroverParallel

/-! ### The set marking oracle -/

/-- The marker table of `groverSetMarkingOracle S`. -/
private abbrev markTab {n : ℕ} (S : Finset (Fin (2 ^ n))) : Fin (2 ^ n) → Fin (2 ^ 1) :=
  fun x => if x ∈ S then (1 : Fin (2 ^ 1)) else 0

private lemma setMarking_val {n : ℕ} (S : Finset (Fin (2 ^ n))) :
    (groverSetMarkingOracle S).1 = ((tableAddPerm (markTab S))⁻¹).permMatrix ℂ := rfl

private lemma fin_two_double : ∀ c : Fin (2 ^ 1), c + c = 0 := by
  decide

private lemma tab_invol {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ 1)) (l : Fin (2 ^ (n + 1))) :
    tableAddPerm f (tableAddPerm f l) = l := by
  apply (splitBasisEquiv n 1).injective
  rw [GroverLowerBound.split_tableAddPerm, GroverLowerBound.split_tableAddPerm]
  refine Prod.ext rfl ?_
  dsimp only
  rw [add_assoc, fin_two_double, add_zero]

private lemma tab_inv_eq {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ 1)) :
    (tableAddPerm f)⁻¹ = tableAddPerm f :=
  Equiv.ext fun l => Equiv.Perm.inv_eq_iff_eq.mpr (tab_invol f l).symm

private lemma setMarking_selfAdjoint {n : ℕ} (S : Finset (Fin (2 ^ n))) :
    ((groverSetMarkingOracle S).1).conjTranspose = (groverSetMarkingOracle S).1 := by
  rw [setMarking_val, Matrix.conjTranspose_permMatrix, inv_inv, tab_inv_eq]

/-! ### Slots -/

/-- The `(n + 1)`-wire register of slot `i` inside the oracle register `r`. -/
private abbrev slotReg {n m Q : ℕ} (r : QRegister ((n + 1) * m) Q) (i : Fin m) :
    QRegister (n + 1) Q :=
  r.compose (QRegister.block (i.val * (n + 1)) (n + 1) (by nlinarith [i.isLt]))

/-- The address read at slot `i` of the basis index `j`. -/
private abbrev addrOf {n m Q : ℕ} (r : QRegister ((n + 1) * m) Q) (i : Fin m)
    (j : Fin (2 ^ Q)) : Fin (2 ^ n) :=
  GroverLowerBound.laddr ((slotReg r i).extractIndex j)

private lemma slot_disjoint {n m Q : ℕ} (r : QRegister ((n + 1) * m) Q) {i j : Fin m}
    (hij : i < j) : (slotReg r i).DisjointWires (slotReg r j) := by
  have hij' : i.val < j.val := hij
  have h : (i.val + 1) * (n + 1) ≤ j.val * (n + 1) :=
    Nat.mul_le_mul_right (n + 1) (Nat.succ_le_of_lt hij')
  exact QRegister.slice_disjoint_of_le r (i.val * (n + 1)) (n + 1) (j.val * (n + 1)) (n + 1)
    (by nlinarith [i.isLt]) (by nlinarith [j.isLt]) (by nlinarith [h])

private lemma slot_selfAdjoint {n m Q : ℕ} (r : QRegister ((n + 1) * m) Q)
    (S : Finset (Fin (2 ^ n))) (i : Fin m) :
    ((slotReg r i).embedMatrix (groverSetMarkingOracle S).1).conjTranspose =
      (slotReg r i).embedMatrix (groverSetMarkingOracle S).1 := by
  rw [← QRegister.embedMatrix_conjTranspose, setMarking_selfAdjoint]

/-- A slot embedding fixes every amplitude whose address is not in `S`. -/
private lemma slot_mulVec_of_not_mem {n Q : ℕ} (R : QRegister (n + 1) Q)
    (S : Finset (Fin (2 ^ n))) (w : Fin (2 ^ Q) → ℂ) (i : Fin (2 ^ Q))
    (h : GroverLowerBound.laddr (R.extractIndex i) ∉ S) :
    (R.embedMatrix (groverSetMarkingOracle S).1 *ᵥ w) i = w i := by
  have hf : markTab S (GroverLowerBound.laddr (R.extractIndex i)) = 0 := if_neg h
  have hinv : (tableAddPerm (markTab S))⁻¹ (R.extractIndex i) = R.extractIndex i :=
    Equiv.Perm.inv_eq_iff_eq.mpr (GroverLowerBound.tableAddPerm_eq_self (markTab S) _ hf).symm
  rw [setMarking_val, GroverLowerBound.perm_apply, hinv]
  exact congrArg w (QRegister.replaceIndex_extractIndex _ _)

/-! ### The product of the slots -/

private lemma embed_list_prod {k Q : ℕ} (r : QRegister k Q) (l : List (Unitary (2 ^ k))) :
    (r.embedUnitary l.prod).1 = (l.map fun U => r.embedMatrix U.1).prod := by
  induction l with
  | nil =>
    rw [List.prod_nil, QRegister.embedUnitary_one, List.map_nil, List.prod_nil]
    rfl
  | cons U t ih =>
    rw [List.prod_cons, QRegister.embedUnitary_mul, List.map_cons, List.prod_cons, ← ih]
    rfl

private lemma oracle_val_list {n m Q : ℕ} (r : QRegister ((n + 1) * m) Q)
    (S : Finset (Fin (2 ^ n))) :
    (r.embedUnitary (groverParallelMarkingOracle m S)).1 =
      (List.ofFn fun i : Fin m => (slotReg r i).embedMatrix (groverSetMarkingOracle S).1).prod := by
  unfold groverParallelMarkingOracle
  rw [embed_list_prod, List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
  exact (congrArg Subtype.val (QRegister.embedUnitary_compose r
    (QRegister.block (i.val * (n + 1)) (n + 1) (by nlinarith [i.isLt]))
    (groverSetMarkingOracle S))).symm

private lemma prod_selfAdjoint {d : Type*} [Fintype d] [DecidableEq d]
    (l : List (Matrix d d ℂ)) (hs : ∀ a ∈ l, aᴴ = a) (hc : l.Pairwise Commute) :
    l.prodᴴ = l.prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.pairwise_cons] at hc
    rw [List.prod_cons, Matrix.conjTranspose_mul,
      ih (fun b hb => hs b (by simp [hb])) hc.2, hs a (by simp)]
    exact ((Commute.list_prod_right t a hc.1).eq).symm

theorem parallelOracle_selfAdjoint {n m Q : ℕ} (r : QRegister ((n + 1) * m) Q)
    (S : Finset (Fin (2 ^ n))) :
    ((r.embedUnitary (groverParallelMarkingOracle m S)).1).conjTranspose =
      (r.embedUnitary (groverParallelMarkingOracle m S)).1 := by
  rw [oracle_val_list]
  refine prod_selfAdjoint _ (List.forall_mem_ofFn_iff.mpr fun i => slot_selfAdjoint r S i) ?_
  rw [List.pairwise_ofFn]
  intro i j hij
  exact QRegister.embedMatrix_comm_of_disjoint _ _ (slot_disjoint r hij) _ _

theorem parallelOracle_mul_self {n m Q : ℕ} (r : QRegister ((n + 1) * m) Q)
    (S : Finset (Fin (2 ^ n))) :
    (r.embedUnitary (groverParallelMarkingOracle m S)).1 *
      (r.embedUnitary (groverParallelMarkingOracle m S)).1 = 1 := by
  have h : ((r.embedUnitary (groverParallelMarkingOracle m S)).1)ᴴ *
      (r.embedUnitary (groverParallelMarkingOracle m S)).1 = 1 :=
    Unitary.star_mul_self_of_mem (r.embedUnitary (groverParallelMarkingOracle m S)).2
  rw [parallelOracle_selfAdjoint r S] at h
  exact h

/-! ### Counting -/

theorem card_targetSets_mem {n k : ℕ} (hk : 1 ≤ k) (x : Fin (2 ^ n)) :
    ((groverTargetSets n k).filter (fun S => x ∈ S)).card = (2 ^ n - 1).choose (k - 1) := by
  have hcard : (Finset.univ.erase x : Finset (Fin (2 ^ n))).card = 2 ^ n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x)]
    simp
  have hxT : ∀ T : Finset (Fin (2 ^ n)), T ⊆ Finset.univ.erase x → x ∉ T :=
    fun T h hx => by simpa using h hx
  rw [← hcard, ← Finset.card_powersetCard]
  apply Finset.card_nbij' (fun S => S.erase x) (fun T => insert x T)
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter, groverTargetSets,
      Finset.mem_powersetCard] at hS
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨Finset.erase_subset_erase x (Finset.subset_univ S), ?_⟩
    rw [Finset.card_erase_of_mem hS.2, hS.1.2]
  · intro T hT
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hT
    simp only [Finset.mem_coe, Finset.mem_filter, groverTargetSets, Finset.mem_powersetCard]
    refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.mem_insert_self x T⟩
    rw [Finset.card_insert_of_notMem (hxT T hT.1), hT.2]
    omega
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter] at hS
    exact Finset.insert_erase hS.2
  · intro T hT
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hT
    exact Finset.erase_insert (hxT T hT.1)

theorem choose_mul_two_pow {n k : ℕ} (hk : 1 ≤ k) :
    (2 ^ n - 1).choose (k - 1) * 2 ^ n = k * (2 ^ n).choose k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hpos : 0 < 2 ^ n := by positivity
  obtain ⟨N', hN'⟩ : ∃ N', 2 ^ n = N' + 1 := ⟨2 ^ n - 1, by omega⟩
  rw [hN']
  simp only [Nat.add_sub_cancel]
  have h := Nat.add_one_mul_choose_eq N' k'
  rw [Nat.mul_comm (N'.choose k') (N' + 1), h]
  exact Nat.mul_comm _ _

/-! ### Locality -/

/-- Some slot address of the basis index `j` lies in `S`. -/
private def Hit {n m Q : ℕ} (r : QRegister ((n + 1) * m) Q) (S : Finset (Fin (2 ^ n)))
    (j : Fin (2 ^ Q)) : Prop :=
  ∃ i : Fin m, addrOf r i j ∈ S

private lemma list_prod_mulVec_fix {d : Type*} [Fintype d] [DecidableEq d]
    (l : List (Matrix d d ℂ)) (j : d)
    (h : ∀ a ∈ l, ∀ w : d → ℂ, (a *ᵥ w) j = w j) (v : d → ℂ) : (l.prod *ᵥ v) j = v j := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.prod_cons, ← Matrix.mulVec_mulVec, h a (by simp) _]
    exact ih (fun b hb => h b (by simp [hb]))

/-- No hit at `j`: the oracle fixes the amplitude at `j`. -/
private lemma oracle_apply_of_not_hit {n m Q : ℕ} (r : QRegister ((n + 1) * m) Q)
    (S : Finset (Fin (2 ^ n))) (v : Fin (2 ^ Q) → ℂ) (j : Fin (2 ^ Q)) (h : ¬ Hit r S j) :
    ((r.embedUnitary (groverParallelMarkingOracle m S)).1 *ᵥ v) j = v j := by
  rw [oracle_val_list]
  exact list_prod_mulVec_fix _ j (List.forall_mem_ofFn_iff.mpr fun i w =>
    slot_mulVec_of_not_mem (slotReg r i) S w j (fun hh => h ⟨i, hh⟩)) v

private lemma mulVec_single_apply {d : Type*} [Fintype d] [DecidableEq d]
    (M : Matrix d d ℂ) (j l : d) : (M *ᵥ Pi.single j (1 : ℂ)) l = M l j := by
  rw [Matrix.mulVec_single_one]
  rfl

/-- The oracle fixes every vector that vanishes on the hit set (this uses self-adjointness). -/
private lemma oracle_fix_off_hit {n m Q : ℕ} (r : QRegister ((n + 1) * m) Q)
    (S : Finset (Fin (2 ^ n))) (u : Fin (2 ^ Q) → ℂ) (hu : ∀ l, Hit r S l → u l = 0) :
    (r.embedUnitary (groverParallelMarkingOracle m S)).1 *ᵥ u = u := by
  funext j
  by_cases hj : Hit r S j
  · rw [hu j hj]
    have hsum : ((r.embedUnitary (groverParallelMarkingOracle m S)).1 *ᵥ u) j =
        ∑ l, (r.embedUnitary (groverParallelMarkingOracle m S)).1 j l * u l := rfl
    rw [hsum]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : Hit r S l
    · rw [hu l hl, mul_zero]
    · have hlj : l ≠ j := by
        rintro rfl
        exact hl hj
      have hOl : (r.embedUnitary (groverParallelMarkingOracle m S)).1 l j = 0 := by
        have h1 := oracle_apply_of_not_hit r S (Pi.single j (1 : ℂ)) l hl
        rw [mulVec_single_apply, Pi.single_eq_of_ne hlj] at h1
        exact h1
      have hOjl : (r.embedUnitary (groverParallelMarkingOracle m S)).1 j l = 0 := by
        have h2 := congrFun (congrFun (parallelOracle_selfAdjoint r S) j) l
        rw [Matrix.conjTranspose_apply, hOl, star_zero] at h2
        exact h2.symm
      rw [hOjl, zero_mul]
  · exact oracle_apply_of_not_hit r S u j hj

/-! ### The squared-sum bound -/

private lemma nsq_sub_unit_le {d : ℕ} (U : Unitary d) (w : Fin d → ℂ) :
    nsq (U.1 *ᵥ w - w) ≤ 4 * nsq w := by
  have h : nsq (U.1 *ᵥ w) = nsq w := GroverLowerBound.nsq_unit U w
  calc nsq (U.1 *ᵥ w - w)
      ≤ ∑ j, (2 * Complex.normSq ((U.1 *ᵥ w) j) + 2 * Complex.normSq (w j)) :=
        Finset.sum_le_sum fun j _ => GroverLowerBound.normSq_sub_le _ _
    _ = 4 * nsq w := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        have h' : ∑ j, Complex.normSq ((U.1 *ᵥ w) j) = nsq w := by
          rw [← h]; rfl
        rw [h']
        show 2 * nsq w + 2 * nsq w = 4 * nsq w
        ring

private lemma sub_eq_of_fix {d : Type*} [Fintype d] [DecidableEq d] (M : Matrix d d ℂ)
    (v u w : d → ℂ) (hv : v = u + w) (hw : M *ᵥ w = w) : M *ᵥ v - v = M *ᵥ u - u := by
  subst hv
  rw [Matrix.mulVec_add, hw]
  abel

private lemma restr_nsq {d : ℕ} (P : Fin d → Prop) [DecidablePred P] (v : Fin d → ℂ) :
    nsq (fun j => if P j then v j else 0) = ∑ j, if P j then Complex.normSq (v j) else 0 := by
  unfold GroverLowerBound.nsq
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : P j <;> simp [h]

open Classical in
private lemma sq_le_hit {n m Q : ℕ} (r : QRegister ((n + 1) * m) Q)
    (S : Finset (Fin (2 ^ n))) (v : Fin (2 ^ Q) → ℂ) :
    nsq ((r.embedUnitary (groverParallelMarkingOracle m S)).1 *ᵥ v - v) ≤
      4 * ∑ j, (if Hit r S j then Complex.normSq (v j) else 0) := by
  obtain ⟨u, hu⟩ : ∃ u : Fin (2 ^ Q) → ℂ, u = fun j => if Hit r S j then v j else 0 :=
    ⟨_, rfl⟩
  have hw : ∀ l, Hit r S l → (v - u) l = 0 := by
    intro l hl
    simp [hu, hl]
  have hv : v = u + (v - u) := by
    funext j
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hfix := oracle_fix_off_hit r S (v - u) hw
  have hnu : nsq u = ∑ j, (if Hit r S j then Complex.normSq (v j) else 0) := by
    rw [hu]
    exact restr_nsq _ _
  calc nsq ((r.embedUnitary (groverParallelMarkingOracle m S)).1 *ᵥ v - v)
      = nsq ((r.embedUnitary (groverParallelMarkingOracle m S)).1 *ᵥ u - u) := by
        rw [sub_eq_of_fix _ v u (v - u) hv hfix]
    _ ≤ 4 * nsq u := nsq_sub_unit_le _ _
    _ = 4 * ∑ j, (if Hit r S j then Complex.normSq (v j) else 0) := by rw [hnu]

open Classical in
private lemma hit_sum_le {n m Q k : ℕ} (hk : 1 ≤ k) (r : QRegister ((n + 1) * m) Q)
    (j : Fin (2 ^ Q)) :
    ∑ S ∈ groverTargetSets n k, (if Hit r S j then (1 : ℝ) else 0) ≤
      (m : ℝ) * (((2 ^ n - 1).choose (k - 1) : ℕ) : ℝ) := by
  calc ∑ S ∈ groverTargetSets n k, (if Hit r S j then (1 : ℝ) else 0)
      ≤ ∑ S ∈ groverTargetSets n k, ∑ i : Fin m, (if addrOf r i j ∈ S then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro S _
        by_cases h : Hit r S j
        · obtain ⟨i, hi⟩ := h
          rw [if_pos ⟨i, hi⟩]
          calc (1 : ℝ) = if addrOf r i j ∈ S then 1 else 0 := (if_pos hi).symm
            _ ≤ ∑ i : Fin m, (if addrOf r i j ∈ S then (1 : ℝ) else 0) :=
              Finset.single_le_sum (f := fun i : Fin m => if addrOf r i j ∈ S then (1 : ℝ) else 0)
                (fun i _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
        · rw [if_neg h]
          exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
    _ = ∑ i : Fin m, ∑ S ∈ groverTargetSets n k, (if addrOf r i j ∈ S then (1 : ℝ) else 0) :=
        Finset.sum_comm
    _ = ∑ _i : Fin m, (((2 ^ n - 1).choose (k - 1) : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_boole]
        exact_mod_cast card_targetSets_mem hk (addrOf r i j)
    _ = (m : ℝ) * (((2 ^ n - 1).choose (k - 1) : ℕ) : ℝ) := by simp
  all_goals exact le_rfl

theorem parallelOracle_sq_sum_le {n m Q : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (r : QRegister ((n + 1) * m) Q) (v : Fin (2 ^ Q) → ℂ) :
    ∑ S ∈ groverTargetSets n k,
        nsq ((r.embedUnitary (groverParallelMarkingOracle m S)).1 *ᵥ v - v) ≤
      4 * ((m : ℝ) * ((2 ^ n - 1).choose (k - 1) : ℕ)) * nsq v := by
  classical
  calc ∑ S ∈ groverTargetSets n k,
        nsq ((r.embedUnitary (groverParallelMarkingOracle m S)).1 *ᵥ v - v)
      ≤ ∑ S ∈ groverTargetSets n k,
          4 * ∑ j, (if Hit r S j then Complex.normSq (v j) else 0) :=
        Finset.sum_le_sum fun S _ => sq_le_hit r S v
    _ = 4 * ∑ j, ∑ S ∈ groverTargetSets n k,
          (if Hit r S j then Complex.normSq (v j) else 0) := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_comm
    _ ≤ 4 * ∑ j, Complex.normSq (v j) * ((m : ℝ) * (((2 ^ n - 1).choose (k - 1) : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro j _
        calc ∑ S ∈ groverTargetSets n k, (if Hit r S j then Complex.normSq (v j) else 0)
            = Complex.normSq (v j) * ∑ S ∈ groverTargetSets n k,
                (if Hit r S j then (1 : ℝ) else 0) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro S _
              split_ifs <;> simp
          _ ≤ Complex.normSq (v j) * ((m : ℝ) * (((2 ^ n - 1).choose (k - 1) : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left (hit_sum_le hk r j) (Complex.normSq_nonneg _)
        all_goals exact le_rfl
    _ = 4 * ((m : ℝ) * ((2 ^ n - 1).choose (k - 1) : ℕ)) * nsq v := by
        rw [← Finset.sum_mul]
        unfold GroverLowerBound.nsq
        ring
  all_goals exact le_rfl

end GroverParallel

#print axioms GroverParallel.parallelOracle_selfAdjoint
#print axioms GroverParallel.parallelOracle_mul_self
#print axioms GroverParallel.card_targetSets_mem
#print axioms GroverParallel.choose_mul_two_pow
#print axioms GroverParallel.parallelOracle_sq_sum_le
