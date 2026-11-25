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
import LowerBounds.Grover.FullQuery
import Mathlib

/-!
# Branch weights over an arbitrary run index

The branch weight `pwS κ V β = κ * V (‖meanS‖²) (avgS) + count * avgS` does not decrease along
`ens`: `pwS_ens_mono_full` for the potential `GroverThreeFifths.Vf` (`FullPotential.lean`) and
`pwS_ens_mono_35` for the piecewise-linear potential `GroverThreeFifths.Vpl` (`Lines.lean`). The
proofs are those of the corresponding monotonicity theorems in `FullBound.lean` and
`ThreeFifthsBound.lean` with `meanV`, `avgW` replaced by `meanS`, `avgS` and the oracle step by
`mean_query_abstract`.
-/

open QuantumComputation.Specs Operator GroverLowerBound
open scoped Matrix

namespace GroverParallel

/-- branch weight with scale κ and potential V -/
noncomputable def pwS {Var ι : Type} [Fintype ι] {Q : ℕ} (κ : ℝ) (V : ℝ → ℝ → ℝ)
    (β : Branch Var ι Q) : ℝ :=
  κ * V (nsq (meanS β.vec)) (avgS β.vec) + (β.count : ℝ) * avgS β.vec

/-! ### Index-generic helper lemmas -/

private lemma avgS_unitary {ι : Type} [Fintype ι] {Q : ℕ} (U : Unitary (2 ^ Q))
    (v : ι → Fin (2 ^ Q) → ℂ) : avgS (fun i => U.1 *ᵥ v i) = avgS v := by
  unfold avgS
  congr 1
  exact Finset.sum_congr rfl fun i _ => nsq_unit U (v i)

private lemma sum_nsq_meanS_measure {ι : Type} [Fintype ι] {Q k : ℕ} (r : QRegister k Q)
    (v : ι → Fin (2 ^ Q) → ℂ) :
    ∑ o : Fin (2 ^ k), nsq (meanS (fun i => (r.computationalBasisMeasurement.1 o) *ᵥ v i)) =
      nsq (meanS v) := by
  simp only [meanS_mulVec]
  exact sum_nsq_measure r.computationalBasisMeasurement (meanS v)

private lemma avgS_measure {ι : Type} [Fintype ι] {Q k : ℕ} (r : QRegister k Q)
    (v : ι → Fin (2 ^ Q) → ℂ) :
    ∑ o : Fin (2 ^ k), avgS (fun i => (r.computationalBasisMeasurement.1 o) *ᵥ v i) =
      avgS v := by
  unfold avgS
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun x _ => sum_nsq_measure r.computationalBasisMeasurement (v x)

private lemma Vf_measureS {ι : Type} [Fintype ι] [Nonempty ι] {Q k : ℕ} (r : QRegister k Q)
    (v : ι → Fin (2 ^ Q) → ℂ) :
    GroverThreeFifths.Vf (nsq (meanS v)) (avgS v) ≤
      ∑ o : Fin (2 ^ k), GroverThreeFifths.Vf (nsq (meanS (fun i => (r.computationalBasisMeasurement.1 o) *ᵥ v i)))
        (avgS (fun i => (r.computationalBasisMeasurement.1 o) *ᵥ v i)) := by
  have h := GroverThreeFifths.Vf_fin_sum
    (fun o : Fin (2 ^ k) =>
      nsq (meanS (fun i => (r.computationalBasisMeasurement.1 o) *ᵥ v i)))
    (fun o => avgS (fun i => (r.computationalBasisMeasurement.1 o) *ᵥ v i))
    (fun o => nsq_nonneg _) (fun o => nsq_meanS_le _)
  rw [sum_nsq_meanS_measure, avgS_measure] at h
  exact h

/-! ### The weight does not decrease -/

theorem pwS_ens_mono_full {Var ι : Type} [DecidableEq Var] [Fintype ι] [Nonempty ι] {Q w : ℕ}
    (G : ι → ℕ → QRegister w Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (hsa : ∀ i c r, (G i c r).conjTranspose = G i c r) (hinv : ∀ i c r, G i c r * G i c r = 1)
    (L : ℝ) (hL : 0 < L)
    (hF2 : ∀ c r (u : Fin (2 ^ Q) → ℂ), ∑ i, nsq (G i c r *ᵥ u - u) ≤ 4 * L * nsq u)
    (t : ℝ) (ht : t ^ 2 = (Fintype.card ι : ℝ) / L) (ht2 : 2 ≤ t)
    (P : LF Var Q w) (E : List (Branch Var ι Q)) :
    (E.map (pwS (2 / Real.arcsin (2 / t)) GroverThreeFifths.Vf)).sum ≤
      ((ens G P E).map (pwS (2 / Real.arcsin (2 / t)) GroverThreeFifths.Vf)).sum := by
  have ht0 : 0 < t := by linarith
  have hκ := GroverThreeFifths.kappa_pos t ht2
  have h := ens_sum_mono G (fun _ : Branch Var ι Q => True)
    (pwS (2 / Real.arcsin (2 / t)) GroverThreeFifths.Vf)
    (fun _ _ _ _ _ => trivial)
    (fun β _ => le_of_eq (by simp [pwS]))
    (fun U β _ => by
      by_cases h : β.live
      · rw [if_pos h]
        refine le_of_eq ?_
        simp only [pwS, meanS_mulVec, nsq_unit, avgS_unitary]
      · rw [if_neg h])
    (fun r β _ => by
      by_cases h : β.live
      · rw [if_pos h]
        have hq := mean_query_abstract (fun i => G i β.count r) (fun i => hsa i β.count r)
          (fun i => hinv i β.count r) L hL (hF2 β.count r) t ht0 ht β.vec
        have h2 : avgS (fun i => G i β.count r *ᵥ β.vec i) = avgS β.vec :=
          avgS_selfInv (fun i => G i β.count r) (fun i => hsa i β.count r)
            (fun i => hinv i β.count r) β.vec
        have h1 := GroverThreeFifths.Vf_query t (nsq (meanS β.vec)) (avgS β.vec)
          (nsq (meanS (fun i => G i β.count r *ᵥ β.vec i)))
          ht2 (nsq_nonneg _) (nsq_meanS_le _) (nsq_nonneg _)
          ((nsq_meanS_le _).trans_eq h2) hq
        simp only [pwS]
        rw [h2]
        push_cast
        linarith
      · rw [if_neg h])
    (fun {k} v r β _ => by
      by_cases h : β.live
      · rw [if_pos h, sum_finRange_map]
        have hV := Vf_measureS (ι := ι) r β.vec
        have h2 := mul_le_mul_of_nonneg_left hV hκ.le
        simp only [pwS, Finset.sum_add_distrib, ← Finset.mul_sum, avgS_measure]
        linarith
      · rw [if_neg h]
        simp)
    P E (fun _ _ => trivial)
  exact h

theorem pwS_ens_mono_35 {Var ι : Type} [DecidableEq Var] [Fintype ι] [Nonempty ι] {Q w : ℕ}
    (G : ι → ℕ → QRegister w Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (hsa : ∀ i c r, (G i c r).conjTranspose = G i c r) (hinv : ∀ i c r, G i c r * G i c r = 1)
    (L : ℝ) (hL : 0 < L)
    (hF2 : ∀ c r (u : Fin (2 ^ Q) → ℂ), ∑ i, nsq (G i c r *ᵥ u - u) ≤ 4 * L * nsq u)
    (t : ℝ) (ht : t ^ 2 = (Fintype.card ι : ℝ) / L) (ht256 : 256 ≤ t)
    (P : LF Var Q w) (E : List (Branch Var ι Q)) :
    (E.map (pwS t GroverThreeFifths.Vpl)).sum ≤ ((ens G P E).map (pwS t GroverThreeFifths.Vpl)).sum := by
  have ht0 : 0 < t := by linarith
  have h := ens_sum_mono G (fun _ : Branch Var ι Q => True) (pwS t GroverThreeFifths.Vpl)
    (fun _ _ _ _ _ => trivial)
    (fun β _ => le_of_eq (by simp [pwS]))
    (fun U β _ => by
      by_cases h : β.live
      · rw [if_pos h]
        refine le_of_eq ?_
        simp only [pwS, meanS_mulVec, nsq_unit, avgS_unitary]
      · rw [if_neg h])
    (fun r β _ => by
      by_cases h : β.live
      · rw [if_pos h]
        have hq := mean_query_abstract (fun i => G i β.count r) (fun i => hsa i β.count r)
          (fun i => hinv i β.count r) L hL (hF2 β.count r) t ht0 ht β.vec
        have h1 := GroverThreeFifths.Vpl_query t (nsq (meanS β.vec)) (avgS β.vec)
          (nsq (meanS (fun i => G i β.count r *ᵥ β.vec i)))
          ht256 (nsq_nonneg _) (nsq_meanS_le _) (nsq_nonneg _) hq
        have h2 : avgS (fun i => G i β.count r *ᵥ β.vec i) = avgS β.vec :=
          avgS_selfInv (fun i => G i β.count r) (fun i => hsa i β.count r)
            (fun i => hinv i β.count r) β.vec
        simp only [pwS]
        rw [h2]
        push_cast
        linarith
      · rw [if_neg h])
    (fun {k} v r β _ => by
      by_cases h : β.live
      · rw [if_pos h, sum_finRange_map]
        have hV := GroverThreeFifths.Vpl_fin_sum
          (fun o : Fin (2 ^ k) =>
            nsq (meanS (fun i => (r.computationalBasisMeasurement.1 o) *ᵥ β.vec i)))
          (fun o => avgS (fun i => (r.computationalBasisMeasurement.1 o) *ᵥ β.vec i))
        rw [sum_nsq_meanS_measure, avgS_measure] at hV
        have h2 := mul_le_mul_of_nonneg_left hV ht0.le
        simp only [pwS, Finset.sum_add_distrib, ← Finset.mul_sum, avgS_measure]
        linarith
      · rw [if_neg h]
        simp)
    P E (fun _ _ => trivial)
  exact h

end GroverParallel

#print axioms GroverParallel.pwS_ens_mono_full
#print axioms GroverParallel.pwS_ens_mono_35
