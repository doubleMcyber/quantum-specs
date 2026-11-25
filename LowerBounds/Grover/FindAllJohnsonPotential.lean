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
import LowerBounds.Grover.FindAllJohnson
import Mathlib

/-!
# The Johnson-scheme potential and `FL`

Definitions for the one-slot find-all floor. `jlam`, `jc`, `jdelta` and `jw` are explicit real
numbers indexed by `N`, `k` and a level, `jpoly N k` is the Lagrange interpolation polynomial through
the points `(jlam N k j, jw N k j)`, and

    FL N k = ∑ i ∈ range (k + 1), jdelta N k i * (1 - (N choose i) / (N choose (k + 1)))

with `jdelta N k i = (N - 2 i) / (2 √((k + 1 - i) (N - k - 1 - i)))`. `Ypot α k` is the polynomial
`jpoly` applied to the Johnson matrix on `(k + 1)`-subsets of `α`, with its diagonal removed, and
`signD x` is the sign vector of the point `x`. `jpoly_eval'` is the interpolation property for
`2 (k + 1) ≤ N`.
-/

namespace GroverParallel
open Polynomial

noncomputable def jlam (N k j : ℕ) : ℝ := ((k : ℝ) + 1 - j) * ((N : ℝ) - k - 1 - j) - j

noncomputable def jc (N k i : ℕ) : ℝ := ((k : ℝ) + 1 - i) * ((N : ℝ) - k - 1 - i)

noncomputable def jdelta (N k i : ℕ) : ℝ := ((N : ℝ) - 2 * i) / (2 * Real.sqrt (jc N k i))

noncomputable def jw (N k j : ℕ) : ℝ := ∑ i ∈ Finset.Ico j (k + 1), jdelta N k i

noncomputable def jpoly (N k : ℕ) : ℝ[X] :=
  Lagrange.interpolate (Finset.range (k + 2)) (jlam N k) (jw N k)

noncomputable def FL (N k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), jdelta N k i * (1 - (N.choose i : ℝ) / (N.choose (k + 1) : ℝ))

noncomputable def Ypot (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ) :
    Matrix (lev α (k + 1)) (lev α (k + 1)) ℝ :=
  aeval (johnson α (k + 1)) (jpoly (Fintype.card α) k) -
    Matrix.diagonal (fun S => aeval (johnson α (k + 1)) (jpoly (Fintype.card α) k) S S)

def signD {α : Type*} [DecidableEq α] {r : ℕ} (x : α) : lev α r → ℝ :=
  fun S => if x ∈ S.1 then -1 else 1

theorem jlam_sub_succ (N k j : ℕ) : jlam N k j - jlam N k (j + 1) = (N : ℝ) - 2 * j := by
  unfold jlam; push_cast; ring

/-- interpolation property, given injectivity of the nodes -/
theorem jpoly_eval (N k j : ℕ) (hinj : Set.InjOn (jlam N k) (Finset.range (k + 2)))
    (hj : j ∈ Finset.range (k + 2)) : (jpoly N k).eval (jlam N k j) = jw N k j := by
  unfold jpoly
  exact Lagrange.eval_interpolate_at_node (jw N k) hinj hj

theorem jlam_sub (N k i j : ℕ) :
    jlam N k i - jlam N k j = ((j : ℝ) - i) * ((N : ℝ) - i - j + 1) := by
  unfold jlam; ring

theorem jlam_injOn (N k : ℕ) (hN : 2 * (k + 1) ≤ N) :
    Set.InjOn (jlam N k) (Finset.range (k + 2)) := by
  intro i hi j hj hij
  have hi' : i < k + 2 := Finset.mem_range.mp hi
  have hj' : j < k + 2 := Finset.mem_range.mp hj
  have h0 : ((j : ℝ) - i) * ((N : ℝ) - i - j + 1) = 0 := by
    rw [← jlam_sub, hij, sub_self]
  have hpos : (0 : ℝ) < (N : ℝ) - i - j + 1 := by
    have : (i : ℝ) + j ≤ N := by exact_mod_cast (by omega : i + j ≤ N)
    linarith
  rcases mul_eq_zero.mp h0 with h | h
  · exact_mod_cast (sub_eq_zero.mp h).symm
  · linarith

/-- interpolation property -/
theorem jpoly_eval' (N k j : ℕ) (hN : 2 * (k + 1) ≤ N) (hj : j < k + 2) :
    (jpoly N k).eval (jlam N k j) = jw N k j :=
  jpoly_eval N k j (jlam_injOn N k hN) (Finset.mem_range.mpr hj)

end GroverParallel

#print axioms GroverParallel.jlam_sub_succ
#print axioms GroverParallel.jpoly_eval
#print axioms GroverParallel.jlam_sub
#print axioms GroverParallel.jlam_injOn
#print axioms GroverParallel.jpoly_eval'
