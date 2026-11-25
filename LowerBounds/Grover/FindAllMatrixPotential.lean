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
import LowerBounds.Grover.ParallelMean
import Mathlib

/-!
# A matrix-weighted potential on run vectors

`gramY Y v = ∑ S, ∑ S', Y S S' Re⟨v S, v S'⟩` for a real coefficient matrix `Y`, and `pwY Y β` adds
the branch's oracle count times its total squared norm. The file proves that unitaries and
measurements leave `gramY` unchanged (`gramY_unitary`, `gramY_measure`), that the total weight of
an ensemble of branches does not decrease along a program when every oracle call lowers `gramY` by
at most the total squared norm (`pwY_ens_mono`), the start value `gramY_init` and that a branch
supported on a single run index has `gramY ≤ 0` when the diagonal of `Y` is not positive
(`gramY_le_zero_of_single`). The run index and the oracle matrices are generic.
-/

open QuantumComputation.Specs Operator GroverLowerBound
open scoped Matrix

namespace GroverParallel

/-- The quadratic potential of the run vectors with coefficient matrix `Y`. -/
noncomputable def gramY {ι : Type} [Fintype ι] {Q : ℕ} (Y : ι → ι → ℝ)
    (v : ι → Fin (2 ^ Q) → ℂ) : ℝ :=
  ∑ S, ∑ S', Y S S' * (∑ j, star (v S j) * v S' j).re

/-- Branch weight: the potential plus the oracle count times the total squared norm. -/
noncomputable def pwY {Var ι : Type} [Fintype ι] {Q : ℕ} (Y : ι → ι → ℝ)
    (β : Branch Var ι Q) : ℝ :=
  gramY Y β.vec + (β.count : ℝ) * ∑ S, nsq (β.vec S)

/-! ### Inner products -/

private lemma innerRe_eq {d : ℕ} (a b : Fin d → ℂ) :
    (∑ j, star (a j) * b j).re = (star a ⬝ᵥ b).re := rfl

private lemma innerRe_mulVec {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d → ℂ) :
    (∑ j, star ((M *ᵥ a) j) * (M *ᵥ b) j).re = (star a ⬝ᵥ ((Mᴴ * M) *ᵥ b)).re := by
  rw [innerRe_eq, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

private lemma innerRe_self {d : ℕ} (a : Fin d → ℂ) :
    (∑ j, star (a j) * a j).re = nsq a := by
  simp [nsq, Complex.re_sum, Complex.normSq_apply]

private lemma innerRe_unit {d : ℕ} (U : Unitary d) (a b : Fin d → ℂ) :
    (∑ j, star ((U.1 *ᵥ a) j) * (U.1 *ᵥ b) j).re = (∑ j, star (a j) * b j).re := by
  have h : U.1ᴴ * U.1 = 1 := Unitary.star_mul_self_of_mem U.2
  rw [innerRe_mulVec, h, Matrix.one_mulVec, innerRe_eq]

private lemma sum_innerRe_measure {d i : ℕ} (M : CompleteMeasurement d i) (a b : Fin d → ℂ) :
    ∑ o, (∑ j, star ((M.1 o *ᵥ a) j) * (M.1 o *ᵥ b) j).re = (∑ j, star (a j) * b j).re := by
  rw [Finset.sum_congr rfl fun o _ => innerRe_mulVec (M.1 o) a b, ← Complex.re_sum,
    ← dotProduct_sum, ← Matrix.sum_mulVec, M.2, Matrix.one_mulVec, innerRe_eq]

private lemma nsq_selfInv' {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (hsa : M.conjTranspose = M)
    (hinv : M * M = 1) (v : Fin d → ℂ) : nsq (M *ᵥ v) = nsq v := by
  rw [nsq_mulVec, hsa, hinv, Matrix.one_mulVec, nsq_eq_dot]

/-! ### The potential under unitaries and measurements -/

theorem gramY_unitary {ι : Type} [Fintype ι] {Q : ℕ} (Y : ι → ι → ℝ) (U : Unitary (2 ^ Q))
    (v : ι → Fin (2 ^ Q) → ℂ) :
    gramY Y (fun S => U.1 *ᵥ v S) = gramY Y v := by
  unfold gramY
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun S' _ => ?_
  rw [innerRe_unit]

theorem gramY_measure {ι : Type} [Fintype ι] {Q k : ℕ} (Y : ι → ι → ℝ) (r : QRegister k Q)
    (v : ι → Fin (2 ^ Q) → ℂ) :
    ∑ o : Fin (2 ^ k), gramY Y (fun S => (r.computationalBasisMeasurement.1 o) *ᵥ v S) =
      gramY Y v := by
  unfold gramY
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S' _ => ?_
  rw [← Finset.mul_sum, sum_innerRe_measure]

private lemma sum_nsq_mulVec_selfInv {ι : Type} [Fintype ι] {Q : ℕ}
    (G : ι → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (hsa : ∀ i, (G i).conjTranspose = G i) (hinv : ∀ i, G i * G i = 1)
    (v : ι → Fin (2 ^ Q) → ℂ) : ∑ S, nsq (G S *ᵥ v S) = ∑ S, nsq (v S) :=
  Finset.sum_congr rfl fun i _ => nsq_selfInv' (G i) (hsa i) (hinv i) (v i)

/-! ### The weight does not decrease -/

theorem pwY_ens_mono {Var ι : Type} [DecidableEq Var] [Fintype ι] {Q w : ℕ}
    (G : ι → ℕ → QRegister w Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (hsa : ∀ i c r, (G i c r).conjTranspose = G i c r) (hinv : ∀ i c r, G i c r * G i c r = 1)
    (Y : ι → ι → ℝ)
    (hH : ∀ c r (v : ι → Fin (2 ^ Q) → ℂ),
      gramY Y v - gramY Y (fun S => G S c r *ᵥ v S) ≤ ∑ S, nsq (v S))
    (P : LF Var Q w) (E : List (Branch Var ι Q)) :
    (E.map (pwY Y)).sum ≤ ((ens G P E).map (pwY Y)).sum := by
  have h := ens_sum_mono G (fun _ : Branch Var ι Q => True) (pwY Y)
    (fun _ _ _ _ _ => trivial)
    (fun β _ => le_of_eq (by simp [pwY]))
    (fun U β _ => by
      by_cases h : β.live
      · rw [if_pos h]
        refine le_of_eq ?_
        have h3 : ∑ i, nsq (U.1 *ᵥ β.vec i) = ∑ i, nsq (β.vec i) :=
          Finset.sum_congr rfl fun i _ => nsq_unit U (β.vec i)
        simp only [pwY, gramY_unitary, h3]
      · rw [if_neg h])
    (fun r β _ => by
      by_cases h : β.live
      · rw [if_pos h]
        have h1 := hH β.count r β.vec
        have h2 := sum_nsq_mulVec_selfInv (fun i => G i β.count r)
          (fun i => hsa i β.count r) (fun i => hinv i β.count r) β.vec
        simp only [pwY]
        rw [h2]
        push_cast
        linarith
      · rw [if_neg h])
    (fun {k} v r β _ => by
      by_cases h : β.live
      · rw [if_pos h, sum_finRange_map]
        have h4 : ∑ o : Fin (2 ^ k), ∑ S, nsq ((r.computationalBasisMeasurement.1 o) *ᵥ β.vec S)
            = ∑ S, nsq (β.vec S) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun S _ =>
            sum_nsq_measure r.computationalBasisMeasurement (β.vec S)
        simp only [pwY, Finset.sum_add_distrib, gramY_measure, ← Finset.mul_sum, h4]
        exact le_of_eq rfl
      · rw [if_neg h]
        simp)
    P E (fun _ _ => trivial)
  exact h

/-! ### The initial state and a single non-zero run -/

theorem gramY_init {ι : Type} [Fintype ι] {Q : ℕ} (Y : ι → ι → ℝ) :
    gramY Y (fun _ => (Pi.single 0 1 : Fin (2 ^ Q) → ℂ)) = ∑ S, ∑ S', Y S S' := by
  unfold gramY
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun S' _ => ?_
  rw [innerRe_self, nsq_init, mul_one]

theorem gramY_le_zero_of_single {ι : Type} [Fintype ι] [DecidableEq ι] {Q : ℕ} (Y : ι → ι → ℝ)
    (hdiag : ∀ S, Y S S ≤ 0) (v : ι → Fin (2 ^ Q) → ℂ) (S₀ : ι) (h : ∀ S, S ≠ S₀ → v S = 0) :
    gramY Y v ≤ 0 := by
  unfold gramY
  rw [Finset.sum_eq_single S₀]
  · rw [Finset.sum_eq_single S₀]
    · rw [innerRe_self]
      exact mul_nonpos_iff.2 (Or.inr ⟨hdiag S₀, nsq_nonneg _⟩)
    · intro S' _ hS'
      simp [h S' hS']
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  · intro S _ hS
    refine Finset.sum_eq_zero fun S' _ => ?_
    simp [h S hS]
  · intro hh
    exact absurd (Finset.mem_univ _) hh

end GroverParallel

#print axioms GroverParallel.gramY_unitary
#print axioms GroverParallel.gramY_measure
#print axioms GroverParallel.pwY_ens_mono
#print axioms GroverParallel.gramY_init
#print axioms GroverParallel.gramY_le_zero_of_single
