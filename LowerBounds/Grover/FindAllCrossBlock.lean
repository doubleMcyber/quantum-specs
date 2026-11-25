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
import LowerBounds.Grover.Defs
import LowerBounds.Grover.FindAllBlockPoly

/-!
# The cross-block inequality

`cross_entry` evaluates the off-diagonal entry of a polynomial in the symbol matrix through the two
eigenvalues (Cayley-Hamilton). `coisometry`: if `4 c b(c)² = 1` at every root `c` of an annihilating
polynomial of `Uᵀ U`, then `W = 2 Uᵀ b(U Uᵀ)` satisfies `W Wᵀ = 1`. `cross_le`: for such a `W`,
twice the `W`-weighted sum of the real inner products of two families of vectors is at most the sum
of their squared norms. `FindAllJohnsonPotentialDrop.lean` uses these facts for the oracle
hypothesis of the potential.
-/

open scoped Matrix Polynomial

namespace GroverParallel

open Polynomial

/-- induction on polynomials: constants, sums, multiplication by `X` -/
private theorem ind_mulX3c {P : ℝ[X] → Prop} (hC : ∀ a, P (C a))
    (hadd : ∀ p q, P p → P q → P (p + q)) (hX : ∀ p, P p → P (p * X)) (p : ℝ[X]) : P p := by
  refine Polynomial.induction_on p hC hadd ?_
  intro n a h
  have : C a * X ^ (n + 1) = C a * X ^ n * X := by ring
  rw [this]
  exact hX _ h

/-! ### Part A: the 2 x 2 values -/

/-- the symbol matrix evaluated at `c` -/
private noncomputable def crossB (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![c - a, 1; c, c - b]

private theorem real_step (m1 m2 P1 P2 : ℝ) (hd : m1 - m2 ≠ 0) :
    (m1 * (P2 * m2) - m2 * (P1 * m1)) / (m1 - m2) = -((P1 - P2) / (m1 - m2)) * (m1 * m2) ∧
    (P1 * m1 - P2 * m2) / (m1 - m2) =
      (m1 * P2 - m2 * P1) / (m1 - m2) + (P1 - P2) / (m1 - m2) * (m1 + m2) := by
  constructor
  · first | (field_simp; ring) | field_simp
  · first | (field_simp; ring) | field_simp

private theorem aeval_crossB (a b c μ₁ μ₂ : ℝ) (htr : μ₁ + μ₂ = 2 * c - a - b)
    (hdet : μ₁ * μ₂ = (c - a) * (c - b) - c) (hne : μ₁ ≠ μ₂) (p : ℝ[X]) :
    aeval (crossB a b c) p =
      ((μ₁ * p.eval μ₂ - μ₂ * p.eval μ₁) / (μ₁ - μ₂)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        ((p.eval μ₁ - p.eval μ₂) / (μ₁ - μ₂)) • crossB a b c := by
  have hd : μ₁ - μ₂ ≠ 0 := sub_ne_zero.mpr hne
  have hBB : crossB a b c * crossB a b c =
      (μ₁ + μ₂) • crossB a b c - (μ₁ * μ₂) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [htr, hdet]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [crossB, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring
  induction p using ind_mulX3c with
  | hC r =>
    have e1 : (μ₁ * r - μ₂ * r) / (μ₁ - μ₂) = r := by
      rw [div_eq_iff hd]; ring
    rw [aeval_C, Algebra.algebraMap_eq_smul_one, eval_C, eval_C, e1, sub_self, zero_div,
      zero_smul, add_zero]
  | hadd p q hp hq =>
    rw [map_add, hp, hq, eval_add, eval_add]
    module
  | hX p hp =>
    obtain ⟨hg, hb⟩ := real_step μ₁ μ₂ (p.eval μ₁) (p.eval μ₂) hd
    rw [map_mul, aeval_X, hp, eval_mul, eval_mul, eval_X, eval_X, hg, hb]
    simp only [add_mul, smul_mul_assoc, Matrix.one_mul, hBB, smul_sub, smul_smul]
    module

theorem cross_entry (a b c μ₁ μ₂ : ℝ) (htr : μ₁ + μ₂ = 2 * c - a - b)
    (hdet : μ₁ * μ₂ = (c - a) * (c - b) - c) (hne : μ₁ ≠ μ₂) (p : ℝ[X]) :
    ((aeval (symA a b) p) 0 1).eval c = (p.eval μ₁ - p.eval μ₂) / (μ₁ - μ₂) := by
  have hmap : (AlgHom.mapMatrix (aeval c : ℝ[X] →ₐ[ℝ] ℝ)) (symA a b) = crossB a b c := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [symA, crossB]
  have h1 : ((aeval (symA a b) p) 0 1).eval c = (aeval (crossB a b c) p) 0 1 := by
    rw [← hmap, Polynomial.aeval_algHom_apply]
    simp [AlgHom.mapMatrix_apply]
  rw [h1, aeval_crossB a b c μ₁ μ₂ htr hdet hne p]
  simp [crossB]

/-! ### Part B: the co-isometry -/

private theorem aeval_transpose_of_symm {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : Mᵀ = M) (p : ℝ[X]) : (aeval M p)ᵀ = aeval M p := by
  induction p using ind_mulX3c with
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

section Part2

variable {i o : Type*} [Fintype i] [DecidableEq i] [Fintype o] [DecidableEq o]

theorem coisometry (U : Matrix o i ℝ) (b : ℝ[X]) (s : Finset ℝ)
    (hann : aeval (Uᵀ * U) (∏ c ∈ s, (X - C c)) = 0)
    (hb : ∀ c ∈ s, 4 * c * (b.eval c) ^ 2 = 1) :
    let W := (2 : ℝ) • (Uᵀ * aeval (U * Uᵀ) b)
    W * Wᵀ = 1 := by
  have hM : (U * Uᵀ)ᵀ = U * Uᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hBm := aeval_transpose_of_symm (U * Uᵀ) hM b
  have hdvd : (∏ c ∈ s, (X - C c)) ∣ (C (4 : ℝ) * (b * b * X) - 1) := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · exact (Polynomial.pairwise_coprime_X_sub_C (s := fun c : ℝ => c)
        Function.injective_id).set_pairwise _
    · intro c hc
      rw [Polynomial.dvd_iff_isRoot]
      show eval c (C (4 : ℝ) * (b * b * X) - 1) = 0
      simp only [eval_sub, eval_mul, eval_C, eval_X, eval_one]
      have := hb c hc
      first | linarith | nlinarith
  obtain ⟨r, hr⟩ := hdvd
  have hz : aeval (Uᵀ * U) (C (4 : ℝ) * (b * b * X) - 1) = 0 := by
    rw [hr, map_mul, hann, zero_mul]
  rw [map_sub, map_mul, aeval_C, map_one, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
    Matrix.one_mul] at hz
  have hT : (4 : ℝ) • aeval (Uᵀ * U) (b * b * X) = 1 := sub_eq_zero.mp hz
  have key : Uᵀ * aeval (U * Uᵀ) b * (aeval (U * Uᵀ) b * U) = aeval (Uᵀ * U) (b * b * X) := by
    have h1 : Uᵀ * aeval (U * Uᵀ) (b * b) = aeval (Uᵀ * U) (b * b) * Uᵀ :=
      intertwine_up U (b * b)
    calc Uᵀ * aeval (U * Uᵀ) b * (aeval (U * Uᵀ) b * U)
        = Uᵀ * (aeval (U * Uᵀ) b * aeval (U * Uᵀ) b) * U := by simp only [Matrix.mul_assoc]
      _ = Uᵀ * aeval (U * Uᵀ) (b * b) * U := by rw [map_mul]
      _ = aeval (Uᵀ * U) (b * b) * Uᵀ * U := by rw [h1]
      _ = aeval (Uᵀ * U) (b * b * X) := by
          rw [map_mul (aeval (Uᵀ * U)) (b * b) X, aeval_X, Matrix.mul_assoc]
  have hWT : ((2 : ℝ) • (Uᵀ * aeval (U * Uᵀ) b))ᵀ = (2 : ℝ) • (aeval (U * Uᵀ) b * U) := by
    rw [Matrix.transpose_smul, Matrix.transpose_mul, hBm, Matrix.transpose_transpose]
  show ((2 : ℝ) • (Uᵀ * aeval (U * Uᵀ) b)) * ((2 : ℝ) • (Uᵀ * aeval (U * Uᵀ) b))ᵀ = 1
  rw [hWT, Matrix.smul_mul, Matrix.mul_smul, smul_smul, key]
  norm_num at hT ⊢
  exact hT

end Part2

/-! ### Part C: the cross-block inequality -/

section Part3

open Matrix

private theorem dot_self_nn {ι : Type*} [Fintype ι] (z : ι → ℝ) : 0 ≤ z ⬝ᵥ z :=
  Finset.sum_nonneg fun k _ => mul_self_nonneg (z k)

private theorem sum3_comm {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℝ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c := by
  calc ∑ a, ∑ b, ∑ c, f a b c = ∑ a, ∑ c, ∑ b, f a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, f a b c := Finset.sum_comm

variable {i o : Type*} [Fintype i] [DecidableEq i] [Fintype o]

private theorem real_cross (W : Matrix i o ℝ) (hW : W * Wᵀ = 1) (x : i → ℝ) (y : o → ℝ) :
    2 * ∑ T, ∑ T', W T T' * (x T * y T') ≤ ∑ T, x T * x T + ∑ T', y T' * y T' := by
  obtain ⟨v, hv⟩ : ∃ v : i → ℝ, v = W *ᵥ y := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : o → ℝ, w = Wᵀ *ᵥ v := ⟨_, rfl⟩
  have h1 : ∑ T, ∑ T', W T T' * (x T * y T') = x ⬝ᵥ v := by
    rw [hv]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun T' _ => by ring
  have h2 : v ⬝ᵥ v = w ⬝ᵥ y := by
    calc v ⬝ᵥ v = v ⬝ᵥ (W *ᵥ y) := by rw [← hv]
      _ = (v ᵥ* W) ⬝ᵥ y := Matrix.dotProduct_mulVec _ _ _
      _ = w ⬝ᵥ y := by rw [hw, Matrix.mulVec_transpose]
  have h3 : W *ᵥ w = v := by
    rw [hw, Matrix.mulVec_mulVec, hW, Matrix.one_mulVec]
  have h4 : w ⬝ᵥ w = v ⬝ᵥ v := by
    calc w ⬝ᵥ w = w ⬝ᵥ (Wᵀ *ᵥ v) := by rw [← hw]
      _ = (w ᵥ* Wᵀ) ⬝ᵥ v := Matrix.dotProduct_mulVec _ _ _
      _ = (W *ᵥ w) ⬝ᵥ v := by rw [Matrix.vecMul_transpose]
      _ = v ⬝ᵥ v := by rw [h3]
  have hc1 : y ⬝ᵥ w = w ⬝ᵥ y := dotProduct_comm _ _
  have hc2 : x ⬝ᵥ v = v ⬝ᵥ x := dotProduct_comm _ _
  have h5 := dot_self_nn (y - w)
  simp only [sub_dotProduct, dotProduct_sub] at h5
  have h6 := dot_self_nn (x - v)
  simp only [sub_dotProduct, dotProduct_sub] at h6
  rw [h1]
  show 2 * (x ⬝ᵥ v) ≤ x ⬝ᵥ x + y ⬝ᵥ y
  linarith

private theorem nsq_swap {d : ℕ} {ι : Type*} [Fintype ι] (a : ι → Fin d → ℂ) :
    ∑ T, GroverLowerBound.nsq (a T) =
      ∑ j, ∑ T, ((a T j).re * (a T j).re + (a T j).im * (a T j).im) := by
  unfold GroverLowerBound.nsq
  simp only [Complex.normSq_apply]
  exact Finset.sum_comm

theorem cross_le {d : ℕ} (W : Matrix i o ℝ) (hW : W * Wᵀ = 1)
    (a : i → Fin d → ℂ) (b : o → Fin d → ℂ) :
    2 * ∑ T, ∑ T', W T T' * (∑ j, star (a T j) * b T' j).re ≤
      ∑ T, GroverLowerBound.nsq (a T) + ∑ T', GroverLowerBound.nsq (b T') := by
  have key : ∀ T T', (∑ j, star (a T j) * b T' j).re =
      ∑ j, ((a T j).re * (b T' j).re + (a T j).im * (b T' j).im) := by
    intro T T'
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.mul_re]
    try ring
  have hj : ∀ j, 2 * ∑ T, ∑ T', W T T' * ((a T j).re * (b T' j).re + (a T j).im * (b T' j).im) ≤
      ∑ T, ((a T j).re * (a T j).re + (a T j).im * (a T j).im) +
        ∑ T', ((b T' j).re * (b T' j).re + (b T' j).im * (b T' j).im) := by
    intro j
    have h1 := real_cross W hW (fun T => (a T j).re) (fun T' => (b T' j).re)
    have h2 := real_cross W hW (fun T => (a T j).im) (fun T' => (b T' j).im)
    beta_reduce at h1 h2
    simp only [mul_add, Finset.sum_add_distrib]
    linarith
  have e1 : ∑ T, ∑ T', W T T' * (∑ j, star (a T j) * b T' j).re =
      ∑ j, ∑ T, ∑ T', W T T' * ((a T j).re * (b T' j).re + (a T j).im * (b T' j).im) := by
    simp_rw [key, Finset.mul_sum]
    exact sum3_comm (fun T T' j =>
      W T T' * ((a T j).re * (b T' j).re + (a T j).im * (b T' j).im))
  rw [e1, nsq_swap a, nsq_swap b, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => hj j

end Part3

#print axioms cross_entry
#print axioms coisometry
#print axioms cross_le

end GroverParallel
