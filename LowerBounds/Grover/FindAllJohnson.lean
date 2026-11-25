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
import Mathlib

/-!
# The Johnson scheme

`lev α r` is the type of `r`-subsets of `α`, `up α r` the inclusion matrix from `r`-subsets to
`(r + 1)`-subsets, and `johnson α r` the adjacency matrix of the Johnson graph (two `r`-sets are
adjacent when they share `r - 1` points). `up_down_comm` and `down_up_zero` give the commutation rule
of `up` and its transpose, and `johnson_eq` writes `johnson α (r + 1)` as `up α r * (up α r)ᵀ - (r + 1) • 1`.
The rest of the file splits the sets at a point `x` into those that contain `x` (`eIn`) and those
that do not (`eOut`) and writes the matrices in this block form.
-/

open scoped Matrix

namespace GroverParallel

/-- the `r`-subsets of `α` -/
abbrev lev (α : Type*) (r : ℕ) := {S : Finset α // S.card = r}

section Defs
variable (α : Type*) [DecidableEq α]

/-- up operator: entry `1` at `(S, T)` when `T ⊆ S` -/
def up (r : ℕ) : Matrix (lev α (r + 1)) (lev α r) ℝ :=
  fun S T => if T.1 ⊆ S.1 then 1 else 0

/-- Johnson adjacency: entry `1` when the two `r`-sets meet in `r - 1` points -/
def johnson (r : ℕ) : Matrix (lev α r) (lev α r) ℝ :=
  fun S S' => if (S.1 ∩ S'.1).card + 1 = r then 1 else 0

end Defs

theorem up_apply {α : Type*} [DecidableEq α] {r : ℕ} (S : lev α (r + 1)) (T : lev α r) :
    up α r S T = if T.1 ⊆ S.1 then 1 else 0 := rfl

theorem johnson_apply {α : Type*} [DecidableEq α] {r : ℕ} (S S' : lev α r) :
    johnson α r S S' = if (S.1 ∩ S'.1).card + 1 = r then 1 else 0 := rfl

/-! ### Counting lemmas -/

private lemma sum_lev_ite {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ) (P : Finset α → Prop)
    [DecidablePred P] :
    (∑ T : lev α r, if P T.1 then (1 : ℝ) else 0) =
      (((Finset.univ : Finset (Finset α)).filter (fun T => T.card = r ∧ P T)).card : ℝ) := by
  have h := Finset.sum_subtype (p := fun T : Finset α => T.card = r) (F := inferInstance)
    ((Finset.univ : Finset (Finset α)).filter (fun T => T.card = r)) (by simp)
    (fun T => if P T then (1 : ℝ) else 0)
  rw [← h, Finset.sum_boole, Finset.filter_filter]

private lemma card_super {α : Type*} [Fintype α] [DecidableEq α] (U : Finset α) (m : ℕ)
    (hU : U.card ≤ m) :
    ((Finset.univ : Finset (Finset α)).filter (fun S => S.card = m ∧ U ⊆ S)).card
      = (Fintype.card α - U.card).choose (m - U.card) := by
  have h1 : (Finset.univ \ U).card = Fintype.card α - U.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ U), Finset.card_univ]
  have key : ∀ V : Finset α, V ⊆ Finset.univ \ U → V ∩ U = ∅ := by
    intro V hv
    ext a
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro ha haU
    have := hv ha
    simp at this
    exact this haU
  rw [← h1, ← Finset.card_powersetCard]
  refine Finset.card_nbij' (fun S => S \ U) (fun V => V ∪ U) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    obtain ⟨hc, hs⟩ := hS
    have := Finset.card_sdiff_add_card_eq_card hs
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.sdiff_subset_sdiff (Finset.subset_univ _) le_rfl, by omega⟩
  · intro V hV
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hV
    obtain ⟨hv, hc⟩ := hV
    have hi := key V hv
    have := Finset.card_union_add_card_inter V U
    rw [hi, Finset.card_empty] at this
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by omega, Finset.subset_union_right⟩
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    exact Finset.sdiff_union_of_subset hS.2
  · intro V hV
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hV
    obtain ⟨hv, hc⟩ := hV
    show (V ∪ U) \ U = V
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact h1
      · exact absurd h1 h2
    · intro ha
      refine ⟨Or.inl ha, ?_⟩
      have := hv ha
      simpa using this

/-- entries of `(up r)ᵀ * up r` -/
private lemma upT_up_apply {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ) (T T' : lev α r) :
    ((up α r)ᵀ * up α r) T T' =
      if T = T' then (Fintype.card α : ℝ) - r
      else if (T.1 ∪ T'.1).card = r + 1 then 1 else 0 := by
  have e0 : ((up α r)ᵀ * up α r) T T' =
      ∑ S : lev α (r + 1), if T.1 ∪ T'.1 ⊆ S.1 then (1 : ℝ) else 0 := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, up_apply]
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases h1 : T.1 ⊆ S.1 <;> by_cases h2 : T'.1 ⊆ S.1 <;>
      simp [h1, h2, Finset.union_subset_iff]
  have e2 : (∑ S : lev α (r + 1), if T.1 ∪ T'.1 ⊆ S.1 then (1 : ℝ) else 0) =
      (((Finset.univ : Finset (Finset α)).filter
        (fun S => S.card = r + 1 ∧ T.1 ∪ T'.1 ⊆ S)).card : ℝ) :=
    sum_lev_ite (r + 1) (fun S => T.1 ∪ T'.1 ⊆ S)
  rw [e0, e2]
  by_cases hT : T = T'
  · subst hT
    simp only [eq_self, ↓reduceIte]
    rw [card_super (T.1 ∪ T.1) (r + 1) (by rw [Finset.union_self]; have := T.2; omega),
      Finset.union_self, T.2]
    have hle : r ≤ Fintype.card α := by
      have := Finset.card_le_univ T.1
      have := T.2
      omega
    have h1 : r + 1 - r = 1 := by omega
    rw [h1, Nat.choose_one_right, Nat.cast_sub hle]
  · simp only [hT, ↓reduceIte]
    have hTU : T.1 ⊆ T.1 ∪ T'.1 := Finset.subset_union_left
    have hT'U : T'.1 ⊆ T.1 ∪ T'.1 := Finset.subset_union_right
    have hge : r + 1 ≤ (T.1 ∪ T'.1).card := by
      by_contra hlt
      have hle1 := Finset.card_le_card hTU
      have hle2 := Finset.card_le_card hT'U
      have hT2 := T.2
      have hT2' := T'.2
      have e1 : T.1 = T.1 ∪ T'.1 := Finset.eq_of_subset_of_card_le hTU (by omega)
      have e2 : T'.1 = T.1 ∪ T'.1 := Finset.eq_of_subset_of_card_le hT'U (by omega)
      exact hT (Subtype.ext (e1.trans e2.symm))
    by_cases hc : (T.1 ∪ T'.1).card = r + 1
    · rw [if_pos hc, card_super (T.1 ∪ T'.1) (r + 1) (by omega), hc]
      simp
    · rw [if_neg hc]
      have h0 : ((Finset.univ : Finset (Finset α)).filter
          (fun S => S.card = r + 1 ∧ T.1 ∪ T'.1 ⊆ S)) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 ?_
        intro S _ hS
        have := Finset.card_le_card hS.2
        have := hS.1
        omega
      rw [h0]
      simp

/-- entries of `up r * (up r)ᵀ` -/
private lemma up_upT_apply {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ) (S S' : lev α (r + 1)) :
    (up α r * (up α r)ᵀ) S S' =
      if S = S' then (r : ℝ) + 1 else if (S.1 ∩ S'.1).card = r then 1 else 0 := by
  have e0 : (up α r * (up α r)ᵀ) S S' =
      ∑ T : lev α r, if T.1 ⊆ S.1 ∩ S'.1 then (1 : ℝ) else 0 := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, up_apply]
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases h1 : T.1 ⊆ S.1 <;> by_cases h2 : T.1 ⊆ S'.1 <;>
      simp [h1, h2, Finset.subset_inter_iff]
  have e2 : (∑ T : lev α r, if T.1 ⊆ S.1 ∩ S'.1 then (1 : ℝ) else 0) =
      (((Finset.univ : Finset (Finset α)).filter
        (fun T => T.card = r ∧ T ⊆ S.1 ∩ S'.1)).card : ℝ) :=
    sum_lev_ite r (fun T => T ⊆ S.1 ∩ S'.1)
  have hf : ((Finset.univ : Finset (Finset α)).filter
      (fun T => T.card = r ∧ T ⊆ S.1 ∩ S'.1)) = Finset.powersetCard r (S.1 ∩ S'.1) := by
    ext T
    simp [Finset.mem_powersetCard, and_comm]
  rw [e0, e2, hf, Finset.card_powersetCard]
  have hSc := S.2
  have hS'c := S'.2
  have hi1 : S.1 ∩ S'.1 ⊆ S.1 := Finset.inter_subset_left
  have hi2 : S.1 ∩ S'.1 ⊆ S'.1 := Finset.inter_subset_right
  have hle1 := Finset.card_le_card hi1
  have hle2 := Finset.card_le_card hi2
  by_cases hSS : S = S'
  · subst hSS
    simp only [eq_self, ↓reduceIte]
    rw [Finset.inter_self, S.2]
    simp [Nat.choose_succ_self_right]
  · simp only [hSS, ↓reduceIte]
    have hne : (S.1 ∩ S'.1).card ≠ r + 1 := by
      intro hc
      apply hSS
      have e1 : S.1 ∩ S'.1 = S.1 := Finset.eq_of_subset_of_card_le hi1 (by omega)
      have e2 : S.1 ∩ S'.1 = S'.1 := Finset.eq_of_subset_of_card_le hi2 (by omega)
      exact Subtype.ext (e1.symm.trans e2)
    by_cases hc : (S.1 ∩ S'.1).card = r
    · rw [if_pos hc, hc]
      simp
    · rw [if_neg hc]
      have hlt : (S.1 ∩ S'.1).card < r := by omega
      rw [Nat.choose_eq_zero_of_lt hlt]
      simp

/-! ### T1 and T3 -/

-- T1: on V_(r+1): down*up - up*down = (|α| - 2(r+1)) I, where the left "up" is from r+1 to r+2
theorem up_down_comm (α : Type*) [Fintype α] [DecidableEq α] (r : ℕ) :
    (up α (r + 1))ᵀ * up α (r + 1) - up α r * (up α r)ᵀ =
      ((Fintype.card α : ℝ) - 2 * (r + 1)) • (1 : Matrix (lev α (r + 1)) (lev α (r + 1)) ℝ) := by
  ext S S'
  rw [Matrix.sub_apply, upT_up_apply, up_upT_apply]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have h := Finset.card_union_add_card_inter S.1 S'.1
  have hS := S.2
  have hS' := S'.2
  by_cases hSS : S = S'
  · subst hSS
    simp only [eq_self, ↓reduceIte]
    push_cast
    ring
  · simp only [hSS, ↓reduceIte]
    split_ifs <;> first | (exfalso; omega) | norm_num

-- T1 at level 0: down*up on V_0 is |α| I
theorem down_up_zero (α : Type*) [Fintype α] [DecidableEq α] :
    (up α 0)ᵀ * up α 0 = (Fintype.card α : ℝ) • (1 : Matrix (lev α 0) (lev α 0) ℝ) := by
  ext T T'
  rw [upT_up_apply]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hT := T.2
  have hT' := T'.2
  have hTT : T = T' :=
    Subtype.ext (by rw [Finset.card_eq_zero.1 hT, Finset.card_eq_zero.1 hT'])
  subst hTT
  simp

-- T3: A = up*down - r I on V_(r+1)
theorem johnson_eq (α : Type*) [Fintype α] [DecidableEq α] (r : ℕ) :
    johnson α (r + 1) = up α r * (up α r)ᵀ - ((r : ℝ) + 1) • 1 := by
  ext S S'
  rw [Matrix.sub_apply, up_upT_apply, johnson_apply]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hS := S.2
  have hS' := S'.2
  by_cases hSS : S = S'
  · subst hSS
    simp only [eq_self, ↓reduceIte]
    rw [Finset.inter_self, S.2]
    simp
  · simp only [hSS, ↓reduceIte]
    split_ifs <;> first | (exfalso; omega) | norm_num

/-! ### Block form at a point -/

/-- the ground set with the point `x` removed -/
abbrev Rest {α : Type*} (x : α) := {a : α // a ≠ x}

section Blocks
variable {α : Type*} [DecidableEq α] (x : α)

private lemma x_notMem_map (T : Finset (Rest x)) :
    x ∉ T.map (Function.Embedding.subtype (· ≠ x)) := by
  intro h
  rw [Finset.mem_map] at h
  obtain ⟨a, _, ha⟩ := h
  exact a.2 ha

/-- the `k`-sets of the rest, with `x` added -/
def eIn {k : ℕ} (T : lev (Rest x) k) : lev α (k + 1) :=
  ⟨insert x (T.1.map (Function.Embedding.subtype (· ≠ x))), by
    rw [Finset.card_insert_of_notMem (x_notMem_map x T.1), Finset.card_map, T.2]⟩

/-- the `(k+1)`-sets of the rest -/
def eOut {k : ℕ} (T : lev (Rest x) (k + 1)) : lev α (k + 1) :=
  ⟨T.1.map (Function.Embedding.subtype (· ≠ x)), by rw [Finset.card_map, T.2]⟩

theorem eIn_injective (k : ℕ) : Function.Injective (eIn x (k := k)) := by
  intro T T' h
  have h1 : insert x (T.1.map (Function.Embedding.subtype (· ≠ x))) =
      insert x (T'.1.map (Function.Embedding.subtype (· ≠ x))) := congrArg Subtype.val h
  have h2 := congrArg (fun s : Finset α => s.erase x) h1
  simp only [Finset.erase_insert (x_notMem_map x T.1),
    Finset.erase_insert (x_notMem_map x T'.1)] at h2
  exact Subtype.ext (Finset.map_injective _ h2)

theorem eOut_injective (k : ℕ) : Function.Injective (eOut x (k := k)) := by
  intro T T' h
  exact Subtype.ext (Finset.map_injective _ (congrArg Subtype.val h))

theorem eIn_or_eOut {k : ℕ} (S : lev α (k + 1)) :
    (∃ T, eIn x T = S) ∨ (∃ T, eOut x T = S) := by
  by_cases hx : x ∈ S.1
  · left
    refine ⟨⟨Finset.subtype (· ≠ x) S.1, ?_⟩, ?_⟩
    · rw [Finset.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem hx, S.2,
        Nat.add_sub_cancel]
    · apply Subtype.ext
      show insert x ((Finset.subtype (· ≠ x) S.1).map (Function.Embedding.subtype (· ≠ x))) = S.1
      rw [Finset.subtype_map, Finset.filter_ne', Finset.insert_erase hx]
  · right
    refine ⟨⟨Finset.subtype (· ≠ x) S.1, ?_⟩, ?_⟩
    · rw [Finset.card_subtype, Finset.filter_ne', Finset.erase_eq_of_notMem hx, S.2]
    · apply Subtype.ext
      show (Finset.subtype (· ≠ x) S.1).map (Function.Embedding.subtype (· ≠ x)) = S.1
      rw [Finset.subtype_map, Finset.filter_ne', Finset.erase_eq_of_notMem hx]

/-- the two cases of `eIn_or_eOut` never hold together -/
theorem eIn_ne_eOut {k : ℕ} (T : lev (Rest x) k) (U : lev (Rest x) (k + 1)) :
    eIn x T ≠ eOut x U := by
  intro h
  have h1 : x ∈ (eIn x T).1 := Finset.mem_insert_self _ _
  rw [h] at h1
  exact x_notMem_map x U.1 h1

private lemma card_inter_ii {k : ℕ} (T T' : lev (Rest x) k) :
    ((eIn x T).1 ∩ (eIn x T').1).card = (T.1 ∩ T'.1).card + 1 := by
  have hx : x ∉ T.1.map (Function.Embedding.subtype (· ≠ x)) ∩
      T'.1.map (Function.Embedding.subtype (· ≠ x)) :=
    fun h => x_notMem_map x T.1 (Finset.mem_inter.1 h).1
  show (insert x (T.1.map (Function.Embedding.subtype (· ≠ x))) ∩
    insert x (T'.1.map (Function.Embedding.subtype (· ≠ x)))).card = _
  rw [← Finset.insert_inter_distrib, Finset.card_insert_of_notMem hx, ← Finset.map_inter,
    Finset.card_map]

private lemma card_inter_io {k : ℕ} (T : lev (Rest x) k) (U : lev (Rest x) (k + 1)) :
    ((eIn x T).1 ∩ (eOut x U).1).card = (T.1 ∩ U.1).card := by
  have hx := x_notMem_map x U.1
  show (insert x (T.1.map (Function.Embedding.subtype (· ≠ x))) ∩
    U.1.map (Function.Embedding.subtype (· ≠ x))).card = _
  rw [Finset.insert_inter_of_notMem hx, ← Finset.map_inter, Finset.card_map]

private lemma card_inter_oi {k : ℕ} (U : lev (Rest x) (k + 1)) (T : lev (Rest x) k) :
    ((eOut x U).1 ∩ (eIn x T).1).card = (T.1 ∩ U.1).card := by
  have hx := x_notMem_map x U.1
  show (U.1.map (Function.Embedding.subtype (· ≠ x)) ∩
    insert x (T.1.map (Function.Embedding.subtype (· ≠ x)))).card = _
  rw [Finset.inter_insert_of_notMem hx, ← Finset.map_inter, Finset.card_map, Finset.inter_comm]

private lemma card_inter_oo {k : ℕ} (U U' : lev (Rest x) (k + 1)) :
    ((eOut x U).1 ∩ (eOut x U').1).card = (U.1 ∩ U'.1).card := by
  show (U.1.map (Function.Embedding.subtype (· ≠ x)) ∩
    U'.1.map (Function.Embedding.subtype (· ≠ x))).card = _
  rw [← Finset.map_inter, Finset.card_map]

private lemma card_inter_eq_iff {γ : Type*} [DecidableEq γ] (A B : Finset γ) (k : ℕ)
    (hA : A.card = k) (hB : B.card = k + 1) : (A ∩ B).card = k ↔ A ⊆ B := by
  constructor
  · intro h
    have hi : A ∩ B ⊆ A := Finset.inter_subset_left
    have : A ∩ B = A := Finset.eq_of_subset_of_card_le hi (by omega)
    exact Finset.inter_eq_left.1 this
  · intro h
    rw [Finset.inter_eq_left.2 h, hA]

variable [Fintype α]

private lemma card_rest : Fintype.card (Rest x) + 1 = Fintype.card α := by
  rw [Fintype.card_of_subtype (p := fun a : α => a ≠ x) (Finset.univ.erase x) (by simp),
    Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
  have : 0 < Fintype.card α := Fintype.card_pos_iff.2 ⟨x⟩
  omega

theorem block_in_in (k : ℕ) :
    (johnson α (k + 1)).submatrix (eIn x) (eIn x) =
      (up (Rest x) k)ᵀ * up (Rest x) k - ((Fintype.card α : ℝ) - (k + 1)) • 1 := by
  ext T T'
  rw [Matrix.submatrix_apply, johnson_apply, card_inter_ii, Matrix.sub_apply, upT_up_apply]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have h := Finset.card_union_add_card_inter T.1 T'.1
  have hT := T.2
  have hT' := T'.2
  have hβ : (Fintype.card (Rest x) : ℝ) + 1 = Fintype.card α := by
    exact_mod_cast card_rest x
  by_cases hTT : T = T'
  · subst hTT
    rw [Finset.inter_self, T.2]
    have hf : ¬ (k + 1 + 1 = k + 1) := by omega
    simp only [hf, eq_self, ↓reduceIte]
    linarith
  · simp only [hTT, ↓reduceIte]
    split_ifs <;> first | (exfalso; omega) | norm_num

theorem block_in_out (k : ℕ) :
    (johnson α (k + 1)).submatrix (eIn x) (eOut x) = (up (Rest x) k)ᵀ := by
  ext T U
  rw [Matrix.submatrix_apply, johnson_apply, card_inter_io, Matrix.transpose_apply, up_apply]
  have hiff := card_inter_eq_iff T.1 U.1 k T.2 U.2
  by_cases h : T.1 ⊆ U.1
  · have hc : (T.1 ∩ U.1).card + 1 = k + 1 := by
      have := hiff.2 h
      omega
    rw [if_pos h, if_pos hc]
  · have hc : ¬ ((T.1 ∩ U.1).card + 1 = k + 1) := by
      intro hc
      exact h (hiff.1 (by omega))
    rw [if_neg h, if_neg hc]

theorem block_out_in (k : ℕ) :
    (johnson α (k + 1)).submatrix (eOut x) (eIn x) = up (Rest x) k := by
  ext U T
  rw [Matrix.submatrix_apply, johnson_apply, card_inter_oi, up_apply]
  have hiff := card_inter_eq_iff T.1 U.1 k T.2 U.2
  by_cases h : T.1 ⊆ U.1
  · have hc : (T.1 ∩ U.1).card + 1 = k + 1 := by
      have := hiff.2 h
      omega
    rw [if_pos h, if_pos hc]
  · have hc : ¬ ((T.1 ∩ U.1).card + 1 = k + 1) := by
      intro hc
      exact h (hiff.1 (by omega))
    rw [if_neg h, if_neg hc]

theorem block_out_out (k : ℕ) :
    (johnson α (k + 1)).submatrix (eOut x) (eOut x) =
      up (Rest x) k * (up (Rest x) k)ᵀ - ((k : ℝ) + 1) • 1 := by
  ext U U'
  rw [Matrix.submatrix_apply, johnson_apply, card_inter_oo, Matrix.sub_apply, up_upT_apply]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hU := U.2
  have hU' := U'.2
  by_cases hUU : U = U'
  · subst hUU
    rw [Finset.inter_self, U.2]
    have hf : ¬ (k + 1 + 1 = k + 1) := by omega
    simp only [hf, eq_self, ↓reduceIte]
    ring
  · simp only [hUU, ↓reduceIte]
    split_ifs <;> first | (exfalso; omega) | norm_num

end Blocks

#print axioms up_down_comm
#print axioms down_up_zero
#print axioms johnson_eq
#print axioms eIn_injective
#print axioms eOut_injective
#print axioms eIn_or_eOut
#print axioms eIn_ne_eOut
#print axioms block_in_in
#print axioms block_in_out
#print axioms block_out_in
#print axioms block_out_out

end GroverParallel
