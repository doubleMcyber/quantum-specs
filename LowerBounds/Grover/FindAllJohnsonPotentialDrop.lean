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
import LowerBounds.Grover.FindAllBlockPoly
import LowerBounds.Grover.FindAllCrossBlock
import LowerBounds.Grover.FindAllOracle
import Mathlib

/-!
# The oracle hypothesis for the Johnson potential

`Ypot_diag`: the potential `Ypot α k` has zero diagonal. `Ypot_HY`: when `2 (k + 1) ≤ card α`,
`HY (Ypot α k) (signD x)` holds for every point `x`. The proof writes the potential in the block
form at `x` (`FindAllJohnson.lean`), builds a matrix `W` with `W Wᵀ = 1` from the interpolation
polynomial (`FindAllCrossBlock.lean`) and applies the cross-block inequality.
-/

open scoped Matrix Polynomial

namespace GroverParallel

open Polynomial

theorem Ypot_diag (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ) (S : lev α (k + 1)) :
    Ypot α k S S = 0 := by
  unfold Ypot
  simp

/-! ### Small helpers -/

private theorem card_rest3d {α : Type*} [Fintype α] [DecidableEq α] (x : α) :
    Fintype.card (Rest x) + 1 = Fintype.card α := by
  rw [Fintype.card_of_subtype (p := fun a : α => a ≠ x) (Finset.univ.erase x) (by simp),
    Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
  have : 0 < Fintype.card α := Fintype.card_pos_iff.2 ⟨x⟩
  omega

private theorem johnson_symm3d {α : Type*} [DecidableEq α] (r : ℕ) (S S' : lev α r) :
    johnson α r S S' = johnson α r S' S := by
  rw [johnson_apply, johnson_apply, Finset.inter_comm]

private theorem ind_mulX3d {P : ℝ[X] → Prop} (hC : ∀ a, P (C a))
    (hadd : ∀ p q, P p → P q → P (p + q)) (hX : ∀ p, P p → P (p * X)) (p : ℝ[X]) : P p := by
  refine Polynomial.induction_on p hC hadd ?_
  intro n a h
  have : C a * X ^ (n + 1) = C a * X ^ n * X := by ring
  rw [this]
  exact hX _ h

private theorem aeval_symm3d {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : Mᵀ = M) (p : ℝ[X]) : (aeval M p)ᵀ = aeval M p := by
  induction p using ind_mulX3d with
  | hC a =>
    rw [aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.transpose_smul, Matrix.transpose_one]
  | hadd p q hp hq =>
    rw [map_add, Matrix.transpose_add, hp, hq]
  | hX p hp =>
    calc (aeval M (p * X))ᵀ = (aeval M p * M)ᵀ := by rw [map_mul, aeval_X]
      _ = Mᵀ * (aeval M p)ᵀ := Matrix.transpose_mul _ _
      _ = M * aeval M p := by rw [hM, hp]
      _ = aeval M (X * p) := by rw [map_mul, aeval_X]
      _ = aeval M (p * X) := by rw [mul_comm]

private theorem signD_eIn {α : Type*} [DecidableEq α] (x : α) {k : ℕ} (T : lev (Rest x) k) :
    signD x (eIn x T) = -1 := by
  have h : x ∈ (eIn x T).1 := Finset.mem_insert_self _ _
  simp [signD, h]

private theorem signD_eOut {α : Type*} [DecidableEq α] (x : α) {k : ℕ} (U : lev (Rest x) (k + 1)) :
    signD x (eOut x U) = 1 := by
  have h : x ∉ (eOut x U).1 := by
    intro h
    have h' : x ∈ U.1.map (Function.Embedding.subtype (· ≠ x)) := h
    rw [Finset.mem_map] at h'
    obtain ⟨a, _, ha⟩ := h'
    exact a.2 ha
  simp [signD, h]

private theorem ip_symm3d {d : ℕ} (x y : Fin d → ℂ) :
    (∑ j, star (x j) * y j).re = (∑ j, star (y j) * x j).re := by
  rw [Complex.re_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.mul_re]
  try ring

private theorem sum2_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (ε : κ ≃ ι) (F : ι → ι → ℝ) :
    ∑ S, ∑ S', F S S' = ∑ s, ∑ s', F (ε s) (ε s') := by
  calc ∑ S, ∑ S', F S S' = ∑ s, ∑ S', F (ε s) S' :=
        (Equiv.sum_comp ε (fun S => ∑ S', F S S')).symm
    _ = ∑ s, ∑ s', F (ε s) (ε s') :=
        Finset.sum_congr rfl fun s _ => (Equiv.sum_comp ε (fun S' => F (ε s) S')).symm

/-! ### The generic block argument -/

private theorem hy_of_blocks {ι : Type} [Fintype ι] {i o : Type} [Fintype i] [DecidableEq i]
    [Fintype o] (ε : i ⊕ o ≃ ι) (Y : ι → ι → ℝ) (D : ι → ℝ) (W : Matrix i o ℝ)
    (hW : W * Wᵀ = 1) {d : ℕ}
    (h1 : ∀ T T', Y (ε (Sum.inl T)) (ε (Sum.inl T')) -
        D (ε (Sum.inl T)) * Y (ε (Sum.inl T)) (ε (Sum.inl T')) * D (ε (Sum.inl T')) = 0)
    (h2 : ∀ U U', Y (ε (Sum.inr U)) (ε (Sum.inr U')) -
        D (ε (Sum.inr U)) * Y (ε (Sum.inr U)) (ε (Sum.inr U')) * D (ε (Sum.inr U')) = 0)
    (h3 : ∀ T U, Y (ε (Sum.inl T)) (ε (Sum.inr U)) -
        D (ε (Sum.inl T)) * Y (ε (Sum.inl T)) (ε (Sum.inr U)) * D (ε (Sum.inr U)) = W T U)
    (h4 : ∀ U T, Y (ε (Sum.inr U)) (ε (Sum.inl T)) -
        D (ε (Sum.inr U)) * Y (ε (Sum.inr U)) (ε (Sum.inl T)) * D (ε (Sum.inl T)) = W T U) :
    HY (d := d) Y D := by
  intro u
  have hsum : ∑ S, ∑ S', (Y S S' - D S * Y S S' * D S') * (∑ j, star (u S j) * u S' j).re =
      ∑ s, ∑ s', (Y (ε s) (ε s') - D (ε s) * Y (ε s) (ε s') * D (ε s')) *
        (∑ j, star (u (ε s) j) * u (ε s') j).re :=
    sum2_equiv ε (fun S S' => (Y S S' - D S * Y S S' * D S') * (∑ j, star (u S j) * u S' j).re)
  have hn : ∑ S, GroverLowerBound.nsq (u S) = ∑ s, GroverLowerBound.nsq (u (ε s)) :=
    (Equiv.sum_comp ε (fun S => GroverLowerBound.nsq (u S))).symm
  rw [hsum, hn]
  simp only [Fintype.sum_sum_type, h1, h2, h3, h4, zero_mul, Finset.sum_const_zero, zero_add,
    add_zero]
  have hc := cross_le W hW (fun T => u (ε (Sum.inl T))) (fun U => u (ε (Sum.inr U)))
  try beta_reduce at hc
  have hs : ∑ U, ∑ T, W T U *
        (∑ j, star (u (ε (Sum.inr U)) j) * u (ε (Sum.inl T)) j).re =
      ∑ T, ∑ U, W T U * (∑ j, star (u (ε (Sum.inl T)) j) * u (ε (Sum.inr U)) j).re := by
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun U _ => ?_)
    rw [ip_symm3d]
  rw [hs]
  linarith

/-! ### The index equivalence and the block form -/

private noncomputable def epsE{α : Type*} [DecidableEq α] (x : α) (k : ℕ) :
    lev (Rest x) k ⊕ lev (Rest x) (k + 1) ≃ lev α (k + 1) :=
  Equiv.ofBijective (Sum.elim (eIn x) (eOut x))
    ⟨by
      rintro (T | U) (T' | U') h
      · exact congrArg Sum.inl (eIn_injective x k h)
      · exact absurd h (eIn_ne_eOut x T U')
      · exact absurd h.symm (eIn_ne_eOut x T' U)
      · exact congrArg Sum.inr (eOut_injective x k h),
    by
      intro S
      rcases eIn_or_eOut x S with ⟨T, h⟩ | ⟨U, h⟩
      · exact ⟨Sum.inl T, h⟩
      · exact ⟨Sum.inr U, h⟩⟩

private theorem epsE_inl {α : Type*} [DecidableEq α] (x : α) {k : ℕ} (T : lev (Rest x) k) :
    epsE x k (Sum.inl T) = eIn x T := rfl

private theorem epsE_inr {α : Type*} [DecidableEq α] (x : α) {k : ℕ} (U : lev (Rest x) (k + 1)) :
    epsE x k (Sum.inr U) = eOut x U := rfl

private theorem sub_eq_bigA {α : Type*} [Fintype α] [DecidableEq α] (x : α) (k : ℕ) :
    (johnson α (k + 1)).submatrix (epsE x k) (epsE x k) =
      bigA (up (Rest x) k) ((Fintype.card α : ℝ) - ((k : ℝ) + 1)) ((k : ℝ) + 1) := by
  ext s s'
  rcases s with T | U <;> rcases s' with T' | U'
  · exact congrFun (congrFun (block_in_in x k) T) T'
  · exact congrFun (congrFun (block_in_out x k) T) U'
  · exact congrFun (congrFun (block_out_in x k) U) T'
  · exact congrFun (congrFun (block_out_out x k) U) U'

/-! ### The values -/

private noncomputable def bpoly (N k : ℕ) : ℝ[X] :=
  (aeval (symA ((N : ℝ) - ((k : ℝ) + 1)) ((k : ℝ) + 1)) (jpoly N k)) 0 1

private theorem val_cond (N k i : ℕ) (hN : 2 * (k + 1) ≤ N) (hi : i ≤ k) :
    4 * jc N k i * ((bpoly N k).eval (jc N k i)) ^ 2 = 1 := by
  have hik : (i : ℝ) ≤ k := by exact_mod_cast hi
  have hNk : 2 * ((k : ℝ) + 1) ≤ N := by exact_mod_cast hN
  have hcpos : 0 < jc N k i := by
    unfold jc
    apply mul_pos <;> linarith
  have hd : (N : ℝ) - 2 * i ≠ 0 := by
    intro h
    linarith
  have hne : jlam N k i ≠ jlam N k (i + 1) := by
    intro h
    have h' := jlam_sub_succ N k i
    rw [h, sub_self] at h'
    exact hd h'.symm
  have htr : jlam N k i + jlam N k (i + 1) =
      2 * jc N k i - ((N : ℝ) - ((k : ℝ) + 1)) - ((k : ℝ) + 1) := by
    unfold jlam jc
    push_cast
    ring
  have hdet : jlam N k i * jlam N k (i + 1) =
      (jc N k i - ((N : ℝ) - ((k : ℝ) + 1))) * (jc N k i - ((k : ℝ) + 1)) - jc N k i := by
    unfold jlam jc
    push_cast
    ring
  have hw : jw N k i - jw N k (i + 1) = jdelta N k i := by
    unfold jw
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : i < k + 1)]
    ring
  unfold bpoly
  rw [cross_entry _ _ _ _ _ htr hdet hne (jpoly N k), jpoly_eval' N k i hN (by omega),
    jpoly_eval' N k (i + 1) hN (by omega), hw, jlam_sub_succ]
  have hs : 0 < Real.sqrt (jc N k i) := Real.sqrt_pos.mpr hcpos
  have hs' : Real.sqrt (jc N k i) ≠ 0 := hs.ne'
  have hsq : Real.sqrt (jc N k i) ^ 2 = jc N k i := Real.sq_sqrt hcpos.le
  have h1 : jdelta N k i / ((N : ℝ) - 2 * i) = 1 / (2 * Real.sqrt (jc N k i)) := by
    unfold jdelta
    field_simp
  rw [h1]
  have h2 : (2 * Real.sqrt (jc N k i)) * (1 / (2 * Real.sqrt (jc N k i))) = 1 :=
    mul_one_div_cancel (by linarith : (0 : ℝ) < 2 * Real.sqrt (jc N k i)).ne'
  calc 4 * jc N k i * (1 / (2 * Real.sqrt (jc N k i))) ^ 2
      = (4 * Real.sqrt (jc N k i) ^ 2) * (1 / (2 * Real.sqrt (jc N k i))) ^ 2 := by rw [hsq]
    _ = ((2 * Real.sqrt (jc N k i)) * (1 / (2 * Real.sqrt (jc N k i)))) ^ 2 := by ring
    _ = 1 := by rw [h2]; norm_num

/-! ### The annihilator -/

private theorem jc_injOn (N k : ℕ) (hN : 2 * (k + 1) ≤ N) :
    Set.InjOn (jc N k) (Finset.range (k + 1)) := by
  intro i hi j hj h
  have hi' : i < k + 1 := Finset.mem_range.mp hi
  have hj' : j < k + 1 := Finset.mem_range.mp hj
  have h0 : ((j : ℝ) - i) * ((N : ℝ) - i - j) = 0 := by
    unfold jc at h
    linear_combination h
  have hpos : (0 : ℝ) < (N : ℝ) - i - j := by
    have : (i : ℝ) + j + 2 ≤ N := by exact_mod_cast (by omega : i + j + 2 ≤ N)
    linarith
  rcases mul_eq_zero.mp h0 with h | h
  · exact_mod_cast (sub_eq_zero.mp h).symm
  · linarith

private theorem ann_prod {α : Type} [Fintype α] [DecidableEq α] (k : ℕ)
    (hN : 2 * (k + 1) ≤ Fintype.card α) (x : α) :
    aeval ((up (Rest x) k)ᵀ * up (Rest x) k)
      (∏ c ∈ (Finset.range (k + 1)).image (jc (Fintype.card α) k), (X - C c)) = 0 := by
  have hM : ((Fintype.card (Rest x) : ℕ) : ℝ) + 1 = (Fintype.card α : ℝ) := by
    exact_mod_cast card_rest3d x
  have hcomm : ∀ r : ℕ, R (Lv := lev (Rest x)) (fun r => up (Rest x) r) r =
      L (Lv := lev (Rest x)) (fun r => up (Rest x) r) r +
        ((Fintype.card (Rest x) : ℝ) - 2 * (r : ℝ)) • 1 := by
    intro r
    cases r with
    | zero =>
      have h0 := down_up_zero (Rest x)
      have e0 : L (Lv := lev (Rest x)) (fun r => up (Rest x) r) 0 = 0 := rfl
      rw [e0, zero_add]
      show (up (Rest x) 0)ᵀ * up (Rest x) 0 = _
      rw [h0]
      simp
    | succ r =>
      have h1 := up_down_comm (Rest x) r
      show (up (Rest x) (r + 1))ᵀ * up (Rest x) (r + 1) =
        up (Rest x) r * (up (Rest x) r)ᵀ +
          ((Fintype.card (Rest x) : ℝ) - 2 * ((r + 1 : ℕ) : ℝ)) • 1
      have e2 : ((Fintype.card (Rest x) : ℝ) - 2 * ((r + 1 : ℕ) : ℝ)) =
          (Fintype.card (Rest x) : ℝ) - 2 * ((r : ℝ) + 1) := by
        simp
      rw [e2, ← h1]
      abel
  have hann := annih_R (Lv := lev (Rest x)) (fun r => up (Rest x) r)
    (Fintype.card (Rest x) : ℝ) hcomm k
  have he : ∀ j ∈ Finset.range (k + 1), (X - C (jc (Fintype.card α) k j)) =
      X - C (e (Fintype.card (Rest x) : ℝ) (k + 1) j) := by
    intro j _
    have : jc (Fintype.card α) k j = e (Fintype.card (Rest x) : ℝ) (k + 1) j := by
      unfold e jc
      push_cast
      linear_combination (-((k : ℝ) + 1 - j)) * hM
    rw [this]
  rw [Finset.prod_image (jc_injOn _ k hN), Finset.prod_congr rfl he]
  exact hann

/-! ### The co-isometry and the cross entries -/

private theorem exists_W {α : Type} [Fintype α] [DecidableEq α] (k : ℕ)
    (hN : 2 * (k + 1) ≤ Fintype.card α) (x : α) :
    ∃ W : Matrix (lev (Rest x) k) (lev (Rest x) (k + 1)) ℝ, W * Wᵀ = 1 ∧
      ∀ T U, 2 * (aeval (johnson α (k + 1)) (jpoly (Fintype.card α) k)) (eIn x T) (eOut x U)
        = W T U := by
  have hsub : (aeval (johnson α (k + 1)) (jpoly (Fintype.card α) k)).submatrix
      (epsE x k) (epsE x k) =
      aeval (bigA (up (Rest x) k) ((Fintype.card α : ℝ) - ((k : ℝ) + 1)) ((k : ℝ) + 1))
        (jpoly (Fintype.card α) k) := by
    rw [← sub_eq_bigA x k]
    exact (Polynomial.aeval_algHom_apply
      (Matrix.reindexAlgEquiv ℝ ℝ (epsE x k).symm) (johnson α (k + 1))
      (jpoly (Fintype.card α) k)).symm
  obtain ⟨c, _, hblock⟩ := block_poly (up (Rest x) k) ((Fintype.card α : ℝ) - ((k : ℝ) + 1))
    ((k : ℝ) + 1) (jpoly (Fintype.card α) k)
  have hentry : ∀ T U, (aeval (johnson α (k + 1)) (jpoly (Fintype.card α) k)) (eIn x T) (eOut x U) =
      ((up (Rest x) k)ᵀ * aeval (up (Rest x) k * (up (Rest x) k)ᵀ)
        (bpoly (Fintype.card α) k)) T U := by
    intro T U
    have h1 := congrFun (congrFun hsub (Sum.inl T)) (Sum.inr U)
    rw [hblock] at h1
    exact h1
  have hb : ∀ c ∈ (Finset.range (k + 1)).image (jc (Fintype.card α) k),
      4 * c * ((bpoly (Fintype.card α) k).eval c) ^ 2 = 1 := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
    exact val_cond (Fintype.card α) k i hN (by have := Finset.mem_range.mp hi; omega)
  have hW := coisometry (up (Rest x) k) (bpoly (Fintype.card α) k)
    ((Finset.range (k + 1)).image (jc (Fintype.card α) k)) (ann_prod k hN x) hb
  refine ⟨(2 : ℝ) • ((up (Rest x) k)ᵀ * aeval (up (Rest x) k * (up (Rest x) k)ᵀ)
    (bpoly (Fintype.card α) k)), hW, ?_⟩
  intro T U
  rw [hentry T U, Matrix.smul_apply, smul_eq_mul]

/-! ### The deliverable -/

private theorem Ypot_offdiag {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ)
    {S S' : lev α (k + 1)} (h : S ≠ S') :
    Ypot α k S S' = (aeval (johnson α (k + 1)) (jpoly (Fintype.card α) k)) S S' := by
  unfold Ypot
  rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ h, sub_zero]

theorem Ypot_HY (α : Type) [Fintype α] [DecidableEq α] (k : ℕ)
    (hN : 2 * (k + 1) ≤ Fintype.card α) (x : α) {d : ℕ} :
    HY (d := d) (Ypot α k) (signD x) := by
  obtain ⟨W, hW, hWe⟩ := exists_W k hN x
  have hsymm : ∀ S S' : lev α (k + 1),
      (aeval (johnson α (k + 1)) (jpoly (Fintype.card α) k)) S S' =
        (aeval (johnson α (k + 1)) (jpoly (Fintype.card α) k)) S' S := by
    intro S S'
    have hM : (johnson α (k + 1))ᵀ = johnson α (k + 1) := by
      ext S S'
      exact johnson_symm3d (k + 1) S' S
    have h := aeval_symm3d _ hM (jpoly (Fintype.card α) k)
    exact (congrFun (congrFun h S) S').symm
  refine hy_of_blocks (epsE x k) (Ypot α k) (signD x) W hW ?_ ?_ ?_ ?_
  · intro T T'
    simp only [epsE_inl, signD_eIn]
    ring
  · intro U U'
    simp only [epsE_inr, signD_eOut]
    ring
  · intro T U
    simp only [epsE_inl, epsE_inr, signD_eIn, signD_eOut]
    rw [Ypot_offdiag k (eIn_ne_eOut x T U), ← hWe T U]
    ring
  · intro U T
    simp only [epsE_inl, epsE_inr, signD_eIn, signD_eOut]
    rw [Ypot_offdiag k (eIn_ne_eOut x T U).symm, hsymm (eOut x U) (eIn x T), ← hWe T U]
    ring

end GroverParallel

#print axioms GroverParallel.Ypot_diag
#print axioms GroverParallel.Ypot_HY
