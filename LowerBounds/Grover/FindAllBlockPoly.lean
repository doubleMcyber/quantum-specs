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
# Polynomials of block matrices

Real matrix algebra used by the Johnson-scheme potential of the find-all floors; nothing here
refers to quantum circuits. For a real matrix `U`, `intertwine_up` and `intertwine_down` move a
polynomial in `U Uᵀ` across `U`, and `block_poly` writes a polynomial in the block matrix
`bigA U a b` as a block matrix of polynomials in `Uᵀ U` and `U Uᵀ`, read off the 2 × 2 symbol
matrix `symA a b`. For a chain of matrices `U r` whose products `L U r` and `R U r` satisfy
`R U r = L U r + (M - 2 r) • 1`, `annih_L` and `annih_R` give annihilating polynomials with roots
`e M r j = (r - j) (M - r - j + 1)`.
-/

open scoped Matrix Polynomial

namespace GroverParallel

open Polynomial

/-- induction on polynomials: constants, sums, multiplication by `X` -/
private theorem ind_mulX {P : ℝ[X] → Prop} (hC : ∀ a, P (C a))
    (hadd : ∀ p q, P p → P q → P (p + q)) (hX : ∀ p, P p → P (p * X)) (p : ℝ[X]) : P p := by
  refine Polynomial.induction_on p hC hadd ?_
  intro n a h
  have : C a * X ^ (n + 1) = C a * X ^ n * X := by ring
  rw [this]
  exact hX _ h

section Part1

variable {i o : Type*} [Fintype i] [DecidableEq i] [Fintype o] [DecidableEq o]

/-- intertwining, up form -/
theorem intertwine_up (U : Matrix o i ℝ) (q : ℝ[X]) :
    Uᵀ * aeval (U * Uᵀ) q = aeval (Uᵀ * U) q * Uᵀ := by
  induction q using ind_mulX with
  | hC a =>
    simp only [aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  | hadd p q hp hq =>
    simp only [map_add, Matrix.mul_add, Matrix.add_mul, hp, hq]
  | hX p hp =>
    simp only [map_mul, aeval_X]
    calc Uᵀ * (aeval (U * Uᵀ) p * (U * Uᵀ)) = (Uᵀ * aeval (U * Uᵀ) p) * (U * Uᵀ) :=
          (Matrix.mul_assoc _ _ _).symm
      _ = (aeval (Uᵀ * U) p * Uᵀ) * (U * Uᵀ) := by rw [hp]
      _ = aeval (Uᵀ * U) p * (Uᵀ * U) * Uᵀ := by simp only [Matrix.mul_assoc]

/-- intertwining, down form -/
theorem intertwine_down (U : Matrix o i ℝ) (q : ℝ[X]) :
    U * aeval (Uᵀ * U) q = aeval (U * Uᵀ) q * U := by
  induction q using ind_mulX with
  | hC a =>
    simp only [aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  | hadd p q hp hq =>
    simp only [map_add, Matrix.mul_add, Matrix.add_mul, hp, hq]
  | hX p hp =>
    simp only [map_mul, aeval_X]
    calc U * (aeval (Uᵀ * U) p * (Uᵀ * U)) = (U * aeval (Uᵀ * U) p) * (Uᵀ * U) :=
          (Matrix.mul_assoc _ _ _).symm
      _ = (aeval (U * Uᵀ) p * U) * (Uᵀ * U) := by rw [hp]
      _ = aeval (U * Uᵀ) p * (U * Uᵀ) * U := by simp only [Matrix.mul_assoc]

/-- the big matrix on `i ⊕ o` -/
noncomputable def bigA (U : Matrix o i ℝ) (a b : ℝ) : Matrix (i ⊕ o) (i ⊕ o) ℝ :=
  Matrix.fromBlocks (Uᵀ * U - a • 1) Uᵀ U (U * Uᵀ - b • 1)

/-- the symbol matrix over `ℝ[X]` -/
noncomputable def symA (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ[X] :=
  !![X - C a, 1; X, X - C b]

private theorem sym_mul (a b : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ[X]) :
    (M * symA a b) 0 0 = M 0 0 * (X - C a) + M 0 1 * X ∧
    (M * symA a b) 0 1 = M 0 0 + M 0 1 * (X - C b) ∧
    (M * symA a b) 1 0 = M 1 0 * (X - C a) + M 1 1 * X ∧
    (M * symA a b) 1 1 = M 1 0 + M 1 1 * (X - C b) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [symA, Matrix.mul_apply, Fin.sum_univ_two]

/-- one multiplication step on the four blocks -/
private theorem step (U : Matrix o i ℝ) (a b : ℝ) (m00 m01 m11 c : ℝ[X]) :
    Matrix.fromBlocks (aeval (Uᵀ * U) m00) (Uᵀ * aeval (U * Uᵀ) m01)
        (U * aeval (Uᵀ * U) c) (aeval (U * Uᵀ) m11) * bigA U a b =
      Matrix.fromBlocks (aeval (Uᵀ * U) (m00 * (X - C a) + m01 * X))
        (Uᵀ * aeval (U * Uᵀ) (m00 + m01 * (X - C b)))
        (U * aeval (Uᵀ * U) (c * (X - C a) + m11))
        (aeval (U * Uᵀ) (X * c + m11 * (X - C b))) := by
  unfold bigA
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [intertwine_up U m01]
    simp only [map_add, map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
      Matrix.mul_assoc]
  · rw [← intertwine_up U m00]
    simp only [map_add, map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
      Matrix.mul_add, Matrix.mul_assoc]
  · rw [← intertwine_down U m11]
    simp only [map_add, map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
      Matrix.mul_add, Matrix.mul_assoc]
  · rw [intertwine_down U c, mul_comm X c]
    simp only [map_add, map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
      Matrix.mul_assoc]

theorem block_poly (U : Matrix o i ℝ) (a b : ℝ) (p : ℝ[X]) :
    ∃ c : ℝ[X], (aeval (symA a b) p) 1 0 = X * c ∧
      aeval (bigA U a b) p =
        Matrix.fromBlocks (aeval (Uᵀ * U) ((aeval (symA a b) p) 0 0))
          (Uᵀ * aeval (U * Uᵀ) ((aeval (symA a b) p) 0 1))
          (U * aeval (Uᵀ * U) c)
          (aeval (U * Uᵀ) ((aeval (symA a b) p) 1 1)) := by
  induction p using ind_mulX with
  | hC r =>
    refine ⟨0, ?_, ?_⟩
    · simp [Matrix.algebraMap_matrix_apply]
    · have h00 : (aeval (symA a b) (C r)) 0 0 = C r := by
        simp [Matrix.algebraMap_matrix_apply, Polynomial.algebraMap_eq]
      have h01 : (aeval (symA a b) (C r)) 0 1 = 0 := by
        simp [Matrix.algebraMap_matrix_apply]
      have h11 : (aeval (symA a b) (C r)) 1 1 = C r := by
        simp [Matrix.algebraMap_matrix_apply, Polynomial.algebraMap_eq]
      rw [h00, h01, h11]
      simp only [aeval_C, map_zero, Matrix.mul_zero, Algebra.algebraMap_eq_smul_one]
      rw [← Matrix.fromBlocks_one]
      simp only [Matrix.fromBlocks_smul, smul_zero]
  | hadd p q hp hq =>
    obtain ⟨c1, h10, hP⟩ := hp
    obtain ⟨c2, h20, hQ⟩ := hq
    refine ⟨c1 + c2, ?_, ?_⟩
    · simp only [map_add, Matrix.add_apply, h10, h20, mul_add]
    · simp only [map_add, Matrix.add_apply, Matrix.mul_add, hP, hQ, Matrix.fromBlocks_add]
  | hX p hp =>
    obtain ⟨c, h10, hP⟩ := hp
    obtain ⟨s00, s01, s10, s11⟩ := sym_mul a b (aeval (symA a b) p)
    have hS : aeval (symA a b) (p * X) = aeval (symA a b) p * symA a b := by
      rw [map_mul, aeval_X]
    have hB : aeval (bigA U a b) (p * X) = aeval (bigA U a b) p * bigA U a b := by
      rw [map_mul, aeval_X]
    refine ⟨c * (X - C a) + (aeval (symA a b) p) 1 1, ?_, ?_⟩
    · rw [hS, s10, h10]
      ring
    · rw [hB, hP, step, hS, s00, s01, s11, h10]

#print axioms intertwine_up
#print axioms intertwine_down
#print axioms block_poly

end Part1

section Part2

variable {Lv : ℕ → Type} [∀ r, Fintype (Lv r)] [∀ r, DecidableEq (Lv r)]

/-- `L 0 = 0`, `L (r + 1) = U r * (U r)ᵀ` -/
noncomputable def L (U : ∀ r, Matrix (Lv (r + 1)) (Lv r) ℝ) : (r : ℕ) → Matrix (Lv r) (Lv r) ℝ
  | 0 => 0
  | r + 1 => U r * (U r)ᵀ

/-- `R r = (U r)ᵀ * U r` -/
noncomputable def R (U : ∀ r, Matrix (Lv (r + 1)) (Lv r) ℝ) (r : ℕ) : Matrix (Lv r) (Lv r) ℝ :=
  (U r)ᵀ * U r

/-- the roots `e r i = (r - i) (M - r - i + 1)` -/
noncomputable def e (M : ℝ) (r j : ℕ) : ℝ := ((r : ℝ) - j) * (M - r - j + 1)

private theorem annih_R_of_L (U : ∀ r, Matrix (Lv (r + 1)) (Lv r) ℝ) (M : ℝ)
    (hcomm : ∀ r : ℕ, R U r = L U r + (M - 2 * (r : ℝ)) • 1) (r : ℕ)
    (h : aeval (L U r) (∏ j ∈ Finset.range (r + 1), (X - C (e M r j))) = 0) :
    aeval (R U r) (∏ j ∈ Finset.range (r + 1), (X - C (e M (r + 1) j))) = 0 := by
  have hR : R U r = aeval (L U r) (X + C (M - 2 * (r : ℝ))) := by
    rw [hcomm r, map_add, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
  have h2 : (∏ j ∈ Finset.range (r + 1), (X - C (e M (r + 1) j))).comp (X + C (M - 2 * (r : ℝ))) =
      ∏ j ∈ Finset.range (r + 1), (X - C (e M r j)) := by
    rw [Polynomial.prod_comp]
    refine Finset.prod_congr rfl fun j _ => ?_
    have he : e M (r + 1) j = e M r j + (M - 2 * (r : ℝ)) := by
      unfold e
      push_cast
      ring
    rw [sub_comp, X_comp, C_comp, he, C_add]
    ring
  rw [hR, ← Polynomial.aeval_comp, h2]
  exact h

theorem annih_L (U : ∀ r, Matrix (Lv (r + 1)) (Lv r) ℝ) (M : ℝ)
    (hcomm : ∀ r : ℕ, R U r = L U r + (M - 2 * (r : ℝ)) • 1) (r : ℕ) :
    aeval (L U r) (∏ j ∈ Finset.range (r + 1), (X - C (e M r j))) = 0 := by
  induction r with
  | zero => simp [L, e]
  | succ r ih =>
    have hR := annih_R_of_L U M hcomm r ih
    rw [Finset.prod_range_succ]
    have he : e M (r + 1) (r + 1) = 0 := by simp [e]
    rw [he, C_0, sub_zero, map_mul, aeval_X]
    have hL : L U (r + 1) = U r * (U r)ᵀ := rfl
    rw [hL]
    have key := intertwine_down (U r) (∏ j ∈ Finset.range (r + 1), (X - C (e M (r + 1) j)))
    have hR' : aeval ((U r)ᵀ * U r)
        (∏ j ∈ Finset.range (r + 1), (X - C (e M (r + 1) j))) = 0 := hR
    rw [hR', Matrix.mul_zero] at key
    rw [← Matrix.mul_assoc, ← key, Matrix.zero_mul]

theorem annih_R (U : ∀ r, Matrix (Lv (r + 1)) (Lv r) ℝ) (M : ℝ)
    (hcomm : ∀ r : ℕ, R U r = L U r + (M - 2 * (r : ℝ)) • 1) (r : ℕ) :
    aeval (R U r) (∏ j ∈ Finset.range (r + 1), (X - C (e M (r + 1) j))) = 0 :=
  annih_R_of_L U M hcomm r (annih_L U M hcomm r)

#print axioms annih_L
#print axioms annih_R

end Part2

end GroverParallel
