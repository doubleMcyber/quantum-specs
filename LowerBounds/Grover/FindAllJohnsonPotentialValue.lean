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
import LowerBounds.Grover.FindAllJohnsonPotential
import LowerBounds.Grover.FindAllTrace
import Mathlib

/-!
# The sum of the entries of the Johnson potential

`Ypot_sum`: when `2 (k + 1) ≤ card α`, the entries of `Ypot α k` sum to
`(card α choose (k + 1)) * FL (card α) k`. The proof evaluates the trace of the interpolation
polynomial with `trace_L` (`FindAllTrace.lean`).
-/

open scoped Matrix Polynomial

namespace GroverParallel

open Polynomial

/-! ### Counting -/

private lemma vsl_ite {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ) (P : Finset α → Prop)
    [DecidablePred P] :
    (∑ T : lev α r, if P T.1 then (1 : ℝ) else 0) =
      (((Finset.univ : Finset (Finset α)).filter (fun T => T.card = r ∧ P T)).card : ℝ) := by
  have h := Finset.sum_subtype (p := fun T : Finset α => T.card = r) (F := inferInstance)
    ((Finset.univ : Finset (Finset α)).filter (fun T => T.card = r)) (by simp)
    (fun T => if P T then (1 : ℝ) else 0)
  rw [← h, Finset.sum_boole, Finset.filter_filter]

private lemma vsl_super {α : Type*} [Fintype α] [DecidableEq α] (U : Finset α) (m : ℕ)
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

/-- column sums of `up`: each `k`-set lies in `N - k` sets of size `k + 1` -/
private lemma up_colsum {α : Type} [Fintype α] [DecidableEq α] (k : ℕ)
    (hk : k ≤ Fintype.card α) (T : lev α k) :
    ∑ S : lev α (k + 1), up α k S T = (Fintype.card α : ℝ) - k := by
  have e0 : ∑ S : lev α (k + 1), up α k S T =
      ∑ S : lev α (k + 1), if T.1 ⊆ S.1 then (1 : ℝ) else 0 := rfl
  have e2 : (∑ S : lev α (k + 1), if T.1 ⊆ S.1 then (1 : ℝ) else 0) =
      (((Finset.univ : Finset (Finset α)).filter
        (fun S => S.card = k + 1 ∧ T.1 ⊆ S)).card : ℝ) :=
    vsl_ite (k + 1) (fun S => T.1 ⊆ S)
  have hT := T.2
  rw [e0, e2, vsl_super T.1 (k + 1) (by omega), hT]
  have h1 : k + 1 - k = 1 := by omega
  rw [h1, Nat.choose_one_right, Nat.cast_sub hk]

/-- row sums of `up`: each `(k+1)`-set contains `k + 1` sets of size `k` -/
private lemma up_rowsum {α : Type} [Fintype α] [DecidableEq α] (k : ℕ) (S : lev α (k + 1)) :
    ∑ T : lev α k, up α k S T = (k : ℝ) + 1 := by
  have e0 : ∑ T : lev α k, up α k S T = ∑ T : lev α k, if T.1 ⊆ S.1 then (1 : ℝ) else 0 := rfl
  have e2 : (∑ T : lev α k, if T.1 ⊆ S.1 then (1 : ℝ) else 0) =
      (((Finset.univ : Finset (Finset α)).filter
        (fun T => T.card = k ∧ T ⊆ S.1)).card : ℝ) :=
    vsl_ite k (fun T => T ⊆ S.1)
  have hf : ((Finset.univ : Finset (Finset α)).filter
      (fun T => T.card = k ∧ T ⊆ S.1)) = Finset.powersetCard k S.1 := by
    ext T
    simp [Finset.mem_powersetCard, and_comm]
  rw [e0, e2, hf, Finset.card_powersetCard, S.2]
  simp [Nat.choose_succ_self_right]

private theorem card_lev' (α : Type) [Fintype α] [DecidableEq α] (r : ℕ) :
    Fintype.card (lev α r) = (Fintype.card α).choose r :=
  Fintype.card_finset_len r

/-! ### Eigenvector of the Johnson matrix -/

private theorem johnson_mulVec_one (α : Type) [Fintype α] [DecidableEq α] (k : ℕ)
    (hk : k ≤ Fintype.card α) :
    johnson α (k + 1) *ᵥ (1 : lev α (k + 1) → ℝ) =
      jlam (Fintype.card α) k 0 • (1 : lev α (k + 1) → ℝ) := by
  have hA := johnson_eq α k
  have h1 : (up α k)ᵀ *ᵥ (1 : lev α (k + 1) → ℝ) = fun _ => (Fintype.card α : ℝ) - k := by
    funext T
    have : ((up α k)ᵀ *ᵥ (1 : lev α (k + 1) → ℝ)) T = ∑ S, up α k S T := by
      simp [Matrix.mulVec, dotProduct]
    rw [this, up_colsum k hk]
  have h2 : (up α k) *ᵥ (fun _ : lev α k => (Fintype.card α : ℝ) - k) =
      fun _ => ((Fintype.card α : ℝ) - k) * ((k : ℝ) + 1) := by
    funext S
    have : ((up α k) *ᵥ (fun _ : lev α k => (Fintype.card α : ℝ) - k)) S =
        ∑ T, up α k S T * ((Fintype.card α : ℝ) - k) := by
      simp [Matrix.mulVec, dotProduct]
    rw [this, ← Finset.sum_mul, up_rowsum]
    ring
  rw [hA, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, h1, h2, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  funext S
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, jlam, Nat.cast_zero]
  ring

private theorem aeval_mulVec_const {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (v : n → ℝ) (c : ℝ) (h : A *ᵥ v = c • v) (q : ℝ[X]) :
    aeval A q *ᵥ v = q.eval c • v := by
  have hpow : ∀ m : ℕ, A ^ m *ᵥ v = c ^ m • v := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul, pow_succ]
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Matrix.add_mulVec, hp, hq, eval_add, add_smul]
  | monomial n a =>
    rw [aeval_monomial, eval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      Matrix.smul_mulVec, hpow, smul_smul]

/-! ### Algebra of the trace coefficients -/

private noncomputable def mm (M i : ℕ) : ℝ :=
  (Nat.choose M i : ℝ) - (if i = 0 then 0 else (Nat.choose M (i - 1) : ℝ))

private theorem mm_sum (M r : ℕ) :
    ∑ i ∈ Finset.range (r + 1), mm M i = (Nat.choose M r : ℝ) := by
  induction r with
  | zero => simp [mm]
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    simp [mm]

private theorem swap_sum (m d : ℕ → ℝ) (K : ℕ) :
    ∑ i ∈ Finset.range (K + 1), m i * ∑ l ∈ Finset.Ico i (K + 1), d l =
      ∑ l ∈ Finset.range (K + 1), d l * ∑ i ∈ Finset.range (l + 1), m i := by
  have h1 : ∀ i, ∑ l ∈ Finset.Ico i (K + 1), d l =
      ∑ l ∈ Finset.range (K + 1), if i ≤ l then d l else 0 := by
    intro i
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext l
    simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
    omega
  have h2 : ∀ i, m i * ∑ l ∈ Finset.Ico i (K + 1), d l =
      ∑ l ∈ Finset.range (K + 1), if i ≤ l then m i * d l else 0 := by
    intro i
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' : l < K + 1 := Finset.mem_range.mp hl
  calc ∑ i ∈ Finset.range (K + 1), (if i ≤ l then m i * d l else 0)
      = ∑ i ∈ Finset.range (l + 1), m i * d l := by
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext i
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
    _ = d l * ∑ i ∈ Finset.range (l + 1), m i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem alg1 (N k : ℕ) :
    ∑ i ∈ Finset.range (k + 2), mm N i * jw N k i =
      ∑ l ∈ Finset.range (k + 1), jdelta N k l * (N.choose l : ℝ) := by
  have h1 : ∑ i ∈ Finset.range (k + 2), mm N i * jw N k i =
      ∑ i ∈ Finset.range (k + 1), mm N i * jw N k i := by
    rw [Finset.sum_range_succ]
    have : jw N k (k + 1) = 0 := by simp [jw]
    rw [this, mul_zero, add_zero]
  rw [h1]
  have h2 := swap_sum (mm N) (jdelta N k) k
  simp only [jw]
  rw [h2]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mm_sum]

private theorem alg2 (N k : ℕ) (hN : 2 * (k + 1) ≤ N) :
    (N.choose (k + 1) : ℝ) * jw N k 0 - ∑ i ∈ Finset.range (k + 2), mm N i * jw N k i =
      (N.choose (k + 1) : ℝ) * FL N k := by
  have hB : (N.choose (k + 1) : ℝ) ≠ 0 := by
    have : 0 < N.choose (k + 1) := Nat.choose_pos (by omega)
    exact_mod_cast this.ne'
  rw [alg1 N k]
  have hw0 : jw N k 0 = ∑ l ∈ Finset.range (k + 1), jdelta N k l := by
    unfold jw
    rw [Finset.range_eq_Ico]
  rw [hw0, Finset.mul_sum, ← Finset.sum_sub_distrib]
  unfold FL
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  first | (field_simp; ring) | field_simp

/-! ### The theorem -/

theorem Ypot_sum (α : Type) [Fintype α] [DecidableEq α] (k : ℕ)
    (hN : 2 * (k + 1) ≤ Fintype.card α) :
    ∑ S, ∑ S', Ypot α k S S' = ((Fintype.card α).choose (k + 1) : ℝ) * FL (Fintype.card α) k := by
  obtain ⟨P, hP⟩ : ∃ P : Matrix (lev α (k + 1)) (lev α (k + 1)) ℝ,
      P = aeval (johnson α (k + 1)) (jpoly (Fintype.card α) k) := ⟨_, rfl⟩
  have hYdef : Ypot α k = P - Matrix.diagonal (fun S => P S S) := by
    rw [hP]; rfl
  -- step 1
  have hY : ∑ S, ∑ S', Ypot α k S S' = ∑ S, ∑ S', P S S' - Matrix.trace P := by
    rw [hYdef]
    simp only [Matrix.sub_apply, Matrix.diagonal_apply, Finset.sum_sub_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rfl
  -- step 2: row sums
  have hrow : ∑ S, ∑ S', P S S' = ((Fintype.card α).choose (k + 1) : ℝ) *
      jw (Fintype.card α) k 0 := by
    have h1 := johnson_mulVec_one α k (by omega)
    have h2 := aeval_mulVec_const (johnson α (k + 1)) 1 _ h1 (jpoly (Fintype.card α) k)
    have h3 : ∀ S, ∑ S', P S S' = jw (Fintype.card α) k 0 := by
      intro S
      have e1 : (P *ᵥ (1 : lev α (k + 1) → ℝ)) S = ∑ S', P S S' := by
        simp [Matrix.mulVec, dotProduct]
      have e2 : (P *ᵥ (1 : lev α (k + 1) → ℝ)) S = jw (Fintype.card α) k 0 := by
        rw [hP, h2]
        simp [jpoly_eval' (Fintype.card α) k 0 hN (by omega)]
      rw [← e1, e2]
    simp only [h3, Finset.sum_const, Finset.card_univ, card_lev', nsmul_eq_mul]
  -- step 3: trace
  have hcomm : ∀ r : ℕ, R (up α) r = L (up α) r +
      (((Fintype.card α : ℕ) : ℝ) - 2 * (r : ℝ)) • 1 := by
    intro r
    cases r with
    | zero =>
      have h := down_up_zero α
      have hL : L (up α) 0 = 0 := rfl
      have hR : R (up α) 0 = (up α 0)ᵀ * up α 0 := rfl
      rw [hL, hR, h]
      simp
    | succ r =>
      have h := up_down_comm α r
      have hL : L (up α) (r + 1) = up α r * (up α r)ᵀ := rfl
      have hR : R (up α) (r + 1) = (up α (r + 1))ᵀ * up α (r + 1) := rfl
      rw [hL, hR,
        show (((Fintype.card α : ℕ) : ℝ) - 2 * ((r + 1 : ℕ) : ℝ)) =
          (Fintype.card α : ℝ) - 2 * ((r : ℝ) + 1) by push_cast; ring]
      exact sub_eq_iff_eq_add'.mp h
  have hcard : ∀ r, Fintype.card (lev α r) = Nat.choose (Fintype.card α) r :=
    fun r => card_lev' α r
  have hPcomp : P = aeval (L (up α) (k + 1))
      ((jpoly (Fintype.card α) k).comp (X - C ((k : ℝ) + 1))) := by
    have hL : L (up α) (k + 1) = up α k * (up α k)ᵀ := rfl
    have hA : aeval (L (up α) (k + 1)) (X - C ((k : ℝ) + 1)) = johnson α (k + 1) := by
      rw [hL, johnson_eq α k, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
    rw [hP, Polynomial.aeval_comp, hA]
  have htr : Matrix.trace P =
      ∑ i ∈ Finset.range (k + 2), mm (Fintype.card α) i * jw (Fintype.card α) k i := by
    rw [hPcomp, trace_L (Lv := lev α) (up α) (Fintype.card α) hcomm hcard (k + 1)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < k + 2 := by
      have := Finset.mem_range.mp hi
      omega
    have hev : e ((Fintype.card α : ℕ) : ℝ) (k + 1) i - ((k : ℝ) + 1) =
        jlam (Fintype.card α) k i := by
      unfold e jlam
      push_cast
      ring
    rw [eval_comp, eval_sub, eval_X, eval_C, hev, jpoly_eval' (Fintype.card α) k i hN hi']
    rfl
  rw [hY, hrow, htr]
  exact alg2 (Fintype.card α) k hN

end GroverParallel

#print axioms GroverParallel.Ypot_sum
