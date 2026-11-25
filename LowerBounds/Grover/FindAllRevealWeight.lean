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
import LowerBounds.Grover.ParallelWeight
import Mathlib

/-!
# The weight argument with a common reference oracle

`pwS_ens_mono_W`: the weight of `ParallelWeight.lean` does not decrease along a program whose oracle
calls have the form `W * G'`, where `W` is a unitary shared by all run indices and the self-inverse
parts `G'` move vectors by a total squared amount of at most `4 L ‖u‖²`. It adapts
`pwS_ens_mono_full` (`ParallelWeight.lean`): the weight depends on the run vectors only through
quantities that a unitary common to all run indices leaves unchanged.
-/

open QuantumComputation.Specs Operator GroverLowerBound
open scoped Matrix

namespace GroverParallel

/-! ### Index-generic helper lemmas -/

private lemma avgS_unitaryW {ι : Type} [Fintype ι] {Q : ℕ} (U : Unitary (2 ^ Q))
    (v : ι → Fin (2 ^ Q) → ℂ) : avgS (fun i => U.1 *ᵥ v i) = avgS v := by
  unfold avgS
  congr 1
  exact Finset.sum_congr rfl fun i _ => nsq_unit U (v i)

private lemma sum_nsq_meanS_measureW {ι : Type} [Fintype ι] {Q k : ℕ} (r : QRegister k Q)
    (v : ι → Fin (2 ^ Q) → ℂ) :
    ∑ o : Fin (2 ^ k), nsq (meanS (fun i => (r.computationalBasisMeasurement.1 o) *ᵥ v i)) =
      nsq (meanS v) := by
  simp only [meanS_mulVec]
  exact sum_nsq_measure r.computationalBasisMeasurement (meanS v)

private lemma avgS_measureW {ι : Type} [Fintype ι] {Q k : ℕ} (r : QRegister k Q)
    (v : ι → Fin (2 ^ Q) → ℂ) :
    ∑ o : Fin (2 ^ k), avgS (fun i => (r.computationalBasisMeasurement.1 o) *ᵥ v i) =
      avgS v := by
  unfold avgS
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun x _ => sum_nsq_measure r.computationalBasisMeasurement (v x)

private lemma Vf_measureSW {ι : Type} [Fintype ι] [Nonempty ι] {Q k : ℕ} (r : QRegister k Q)
    (v : ι → Fin (2 ^ Q) → ℂ) :
    GroverThreeFifths.Vf (nsq (meanS v)) (avgS v) ≤
      ∑ o : Fin (2 ^ k), GroverThreeFifths.Vf (nsq (meanS (fun i => (r.computationalBasisMeasurement.1 o) *ᵥ v i)))
        (avgS (fun i => (r.computationalBasisMeasurement.1 o) *ᵥ v i)) := by
  have h := GroverThreeFifths.Vf_fin_sum
    (fun o : Fin (2 ^ k) =>
      nsq (meanS (fun i => (r.computationalBasisMeasurement.1 o) *ᵥ v i)))
    (fun o => avgS (fun i => (r.computationalBasisMeasurement.1 o) *ᵥ v i))
    (fun o => nsq_nonneg _) (fun o => nsq_meanS_le _)
  rw [sum_nsq_meanS_measureW, avgS_measureW] at h
  exact h

/-! ### The weight does not decrease -/

theorem pwS_ens_mono_W {Var ι : Type} [DecidableEq Var] [Fintype ι] [Nonempty ι] {Q w : ℕ}
    (G G' : ι → ℕ → QRegister w Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (W : ℕ → QRegister w Q → Unitary (2 ^ Q))
    (hG : ∀ i c r, G i c r = (W c r).1 * G' i c r)
    (hsa : ∀ i c r, (G' i c r).conjTranspose = G' i c r) (hinv : ∀ i c r, G' i c r * G' i c r = 1)
    (L : ℝ) (hL : 0 < L)
    (hF2 : ∀ c r (u : Fin (2 ^ Q) → ℂ), ∑ i, nsq (G' i c r *ᵥ u - u) ≤ 4 * L * nsq u)
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
        simp only [pwS, meanS_mulVec, nsq_unit, avgS_unitaryW]
      · rw [if_neg h])
    (fun r β _ => by
      by_cases h : β.live
      · rw [if_pos h]
        have hq := mean_query_abstract (fun i => G' i β.count r) (fun i => hsa i β.count r)
          (fun i => hinv i β.count r) L hL (hF2 β.count r) t ht0 ht β.vec
        have h2' : avgS (fun i => G' i β.count r *ᵥ β.vec i) = avgS β.vec :=
          avgS_selfInv (fun i => G' i β.count r) (fun i => hsa i β.count r)
            (fun i => hinv i β.count r) β.vec
        -- the common unitary W changes neither the mean's norm nor the average mass
        have hGv : (fun i => G i β.count r *ᵥ β.vec i) =
            fun i => (W β.count r).1 *ᵥ (G' i β.count r *ᵥ β.vec i) := by
          funext i
          rw [hG, Matrix.mulVec_mulVec]
        have hm : nsq (meanS (fun i => G i β.count r *ᵥ β.vec i)) =
            nsq (meanS (fun i => G' i β.count r *ᵥ β.vec i)) := by
          rw [hGv, meanS_mulVec, nsq_unit]
        have h2 : avgS (fun i => G i β.count r *ᵥ β.vec i) = avgS β.vec := by
          rw [hGv, avgS_unitaryW, h2']
        have h1 := GroverThreeFifths.Vf_query t (nsq (meanS β.vec)) (avgS β.vec)
          (nsq (meanS (fun i => G i β.count r *ᵥ β.vec i)))
          ht2 (nsq_nonneg _) (nsq_meanS_le _) (nsq_nonneg _)
          ((nsq_meanS_le _).trans_eq h2) (by rw [hm]; exact hq)
        simp only [pwS]
        rw [h2]
        push_cast
        linarith
      · rw [if_neg h])
    (fun {k} v r β _ => by
      by_cases h : β.live
      · rw [if_pos h, sum_finRange_map]
        have hV := Vf_measureSW (ι := ι) r β.vec
        have h2 := mul_le_mul_of_nonneg_left hV hκ.le
        simp only [pwS, Finset.sum_add_distrib, ← Finset.mul_sum, avgS_measureW]
        linarith
      · rw [if_neg h]
        simp)
    P E (fun _ _ => trivial)
  exact h

end GroverParallel

#print axioms GroverParallel.pwS_ens_mono_W
