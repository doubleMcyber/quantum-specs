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
import LowerBounds.Grover.FindAllBlockPoly

/-!
# Traces of polynomials in the level products

`trace_L`: for a chain of matrices as in `FindAllBlockPoly.lean` whose level `r` has `M choose r`
elements, the trace of a polynomial `q` in `L U r` is a sum over the roots `e M r i`, each with
multiplicity `M choose i - M choose (i - 1)`. `FindAllJohnsonPotentialValue.lean` uses it to sum the
entries of the potential.
-/

open scoped Matrix Polynomial

namespace GroverParallel

open Polynomial

/-- coefficient `choose M i - choose M (i - 1)` (with the second term `0` at `i = 0`) -/
private noncomputable def coef (M i : ℕ) : ℝ :=
  (Nat.choose M i : ℝ) - (if i = 0 then 0 else (Nat.choose M (i - 1) : ℝ))

private theorem coef_sum (M r : ℕ) :
    ∑ i ∈ Finset.range (r + 1), coef M i = (Nat.choose M r : ℝ) := by
  induction r with
  | zero => simp [coef]
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    simp [coef]

private theorem decomp (q : ℝ[X]) : ∃ h : ℝ[X], q = C (q.eval 0) + X * h := by
  obtain ⟨h, hh⟩ := Polynomial.X_dvd_sub_C (p := q)
  refine ⟨h, ?_⟩
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  linear_combination hh

private theorem aeval_split {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (q h : ℝ[X]) (hq : q = C (q.eval 0) + X * h) :
    aeval A q = (q.eval 0) • (1 : Matrix n n ℝ) + A * aeval A h := by
  conv_lhs => rw [hq]
  rw [map_add, map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one]

private theorem eval_split (q h : ℝ[X]) (hq : q = C (q.eval 0) + X * h) (x : ℝ) :
    q.eval x = q.eval 0 + x * h.eval x := by
  conv_lhs => rw [hq]
  simp only [eval_add, eval_C, eval_mul, eval_X]

section Part3

variable {Lv : ℕ → Type} [∀ r, Fintype (Lv r)] [∀ r, DecidableEq (Lv r)]

private theorem aeval_R (U : ∀ r, Matrix (Lv (r + 1)) (Lv r) ℝ) (M : ℕ)
    (hcomm : ∀ r : ℕ, R U r = L U r + ((M : ℝ) - 2 * (r : ℝ)) • 1) (r : ℕ) (g : ℝ[X]) :
    aeval (R U r) g = aeval (L U r) (g.comp (X + C ((M : ℝ) - 2 * (r : ℝ)))) := by
  have hR : R U r = aeval (L U r) (X + C ((M : ℝ) - 2 * (r : ℝ))) := by
    rw [hcomm r, map_add, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
  rw [Polynomial.aeval_comp, ← hR]

private theorem trace_aux (U : ∀ r, Matrix (Lv (r + 1)) (Lv r) ℝ) (M : ℕ)
    (hcomm : ∀ r : ℕ, R U r = L U r + ((M : ℝ) - 2 * (r : ℝ)) • 1)
    (hcard : ∀ r, Fintype.card (Lv r) = Nat.choose M r) (r : ℕ) :
    ∀ q : ℝ[X], Matrix.trace (aeval (L U r) q) =
      ∑ i ∈ Finset.range (r + 1), coef M i * q.eval (e (M : ℝ) r i) := by
  induction r with
  | zero =>
    intro q
    obtain ⟨h, hq⟩ := decomp q
    have hL : L U 0 = 0 := rfl
    rw [aeval_split (L U 0) q h hq, hL]
    simp [e, coef, hcard]
  | succ r ih =>
    intro q
    obtain ⟨h, hq⟩ := decomp q
    have hL : L U (r + 1) = U r * (U r)ᵀ := rfl
    have hT : Matrix.trace (aeval (L U (r + 1)) q) =
        q.eval 0 * (Nat.choose M (r + 1) : ℝ) + Matrix.trace (aeval (R U r) (X * h)) := by
      rw [aeval_split (L U (r + 1)) q h hq, Matrix.trace_add, Matrix.trace_smul,
        Matrix.trace_one, hcard, smul_eq_mul]
      congr 1
      rw [hL]
      calc Matrix.trace (U r * (U r)ᵀ * aeval (U r * (U r)ᵀ) h)
          = Matrix.trace (U r * ((U r)ᵀ * aeval (U r * (U r)ᵀ) h)) := by rw [Matrix.mul_assoc]
        _ = Matrix.trace (U r * (aeval ((U r)ᵀ * U r) h * (U r)ᵀ)) := by
            rw [intertwine_up]
        _ = Matrix.trace ((aeval ((U r)ᵀ * U r) h * (U r)ᵀ) * U r) :=
            Matrix.trace_mul_comm _ _
        _ = Matrix.trace (aeval ((U r)ᵀ * U r) h * ((U r)ᵀ * U r)) := by rw [Matrix.mul_assoc]
        _ = Matrix.trace (aeval (R U r) (X * h)) := by
            rw [mul_comm X h, map_mul, aeval_X]; rfl
    have hkey : ∀ i, ((X * h).comp (X + C ((M : ℝ) - 2 * (r : ℝ)))).eval (e (M : ℝ) r i) =
        q.eval (e (M : ℝ) (r + 1) i) - q.eval 0 := by
      intro i
      have he : e (M : ℝ) (r + 1) i = e (M : ℝ) r i + ((M : ℝ) - 2 * (r : ℝ)) := by
        unfold e; push_cast; ring
      rw [eval_split q h hq (e (M : ℝ) (r + 1) i), he]
      simp only [eval_comp, eval_mul, eval_X, eval_add, eval_C]
      ring
    have hsum : ∑ i ∈ Finset.range (r + 1), coef M i *
          ((X * h).comp (X + C ((M : ℝ) - 2 * (r : ℝ)))).eval (e (M : ℝ) r i) =
        ∑ i ∈ Finset.range (r + 1), coef M i * q.eval (e (M : ℝ) (r + 1) i) -
          q.eval 0 * ∑ i ∈ Finset.range (r + 1), coef M i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hkey i]
      ring
    rw [hT, aeval_R U M hcomm r (X * h), ih, hsum, coef_sum, Finset.sum_range_succ _ (r + 1)]
    have he0 : e (M : ℝ) (r + 1) (r + 1) = 0 := by simp [e]
    have hc : coef M (r + 1) = (Nat.choose M (r + 1) : ℝ) - (Nat.choose M r : ℝ) := by
      simp [coef]
    rw [he0, hc]
    ring

theorem trace_L (U : ∀ r, Matrix (Lv (r + 1)) (Lv r) ℝ) (M : ℕ)
    (hcomm : ∀ r : ℕ, R U r = L U r + ((M : ℝ) - 2 * (r : ℝ)) • 1)
    (hcard : ∀ r, Fintype.card (Lv r) = Nat.choose M r) (r : ℕ) (q : ℝ[X]) :
    Matrix.trace (aeval (L U r) q) =
      ∑ i ∈ Finset.range (r + 1),
        (((Nat.choose M i : ℝ) - (if i = 0 then 0 else (Nat.choose M (i - 1) : ℝ))) *
          q.eval (e (M : ℝ) r i)) :=
  trace_aux U M hcomm hcard r q

#print axioms trace_L

end Part3

end GroverParallel
