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
import LowerBounds.Grover.ParallelDefs
import LowerBounds.Grover.Cost
import Mathlib

/-!
# End bound and cost sum over an arbitrary run index

`nsq_meanS_split`, `sum_meanS_le` and `cwaS_sum` extend `GroverThreeFifths.nsq_meanV_split`,
`GroverThreeFifths.sum_meanV_le` and `GroverThreeFifths.cwa_sum` from the run index `Fin (2 ^ n)`
to an arbitrary finite index type, and from at most one good run per branch to at most `κ` good
runs per branch.
-/

open QuantumComputation.Specs Operator ResourceCounting GroverLowerBound
open scoped Matrix QHLExpectation ComplexOrder MatrixOrder

namespace GroverParallel

/-- Cauchy-Schwarz on a finset of complex numbers. -/
private lemma cs_bound {ι : Type} (s : Finset ι) (f : ι → ℂ) (N : ℝ) (hN : (s.card : ℝ) ≤ N) :
    Complex.normSq (∑ x ∈ s, f x) ≤ N * ∑ x ∈ s, Complex.normSq (f x) := by
  rw [Complex.normSq_eq_norm_sq]
  have h2 : ‖∑ x ∈ s, f x‖ ≤ ∑ x ∈ s, ‖f x‖ := norm_sum_le _ _
  have h3 : ‖∑ x ∈ s, f x‖ ^ 2 ≤ (∑ x ∈ s, ‖f x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h4 := sq_sum_le_card_mul_sum_sq (s := s) (f := fun x => ‖f x‖)
  have h6 : ∑ x ∈ s, ‖f x‖ ^ 2 = ∑ x ∈ s, Complex.normSq (f x) :=
    Finset.sum_congr rfl fun x _ => (Complex.normSq_eq_norm_sq _).symm
  have h7 : 0 ≤ ∑ x ∈ s, ‖f x‖ ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
  rw [h6] at h4 h7
  calc ‖∑ x ∈ s, f x‖ ^ 2 ≤ _ := h3
    _ ≤ _ := h4
    _ ≤ N * ∑ x ∈ s, Complex.normSq (f x) := mul_le_mul_of_nonneg_right hN h7

/-- Cauchy-Schwarz and the splitting of the mean, coordinatewise and then summed. -/
theorem nsq_meanS_split {ι : Type} [Fintype ι] [DecidableEq ι] {Q : ℕ} (v : ι → Fin (2 ^ Q) → ℂ)
    (T : Finset ι) (κ : ℕ) (hT : T.card ≤ κ) :
    nsq (meanS v) ≤ 2 * κ / (Fintype.card ι : ℝ) ^ 2 * ∑ i ∈ T, nsq (v i) +
      2 / (Fintype.card ι : ℝ) * ∑ i ∈ Tᶜ, nsq (v i) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hT0 : T = ∅ := Finset.eq_empty_of_isEmpty T
    have hTc : Tᶜ = ∅ := Finset.eq_empty_of_isEmpty _
    rw [hTc, hT0]
    simp [nsq, meanS]
  have hBpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  set B : ℝ := (Fintype.card ι : ℝ) with hBdef
  have key : ∀ j, Complex.normSq (meanS v j) ≤
      2 * κ / B ^ 2 * ∑ x ∈ T, Complex.normSq (v x j) +
        2 / B * ∑ x ∈ Tᶜ, Complex.normSq (v x j) := by
    intro j
    have hc : ((Fintype.card ι : ℕ) : ℂ)⁻¹ = ((B⁻¹ : ℝ) : ℂ) := by
      rw [hBdef]; simp
    have h1 : Complex.normSq (meanS v j) = (B⁻¹) ^ 2 * Complex.normSq (∑ x, v x j) := by
      unfold meanS
      rw [hc, Complex.normSq_mul, Complex.normSq_ofReal]
      ring
    set a : ℂ := ∑ x ∈ T, v x j with ha
    set b : ℂ := ∑ x ∈ Tᶜ, v x j with hb
    have hsplit : ∑ x, v x j = a + b := (Finset.sum_add_sum_compl T (fun x => v x j)).symm
    have hadd : Complex.normSq (a + b) ≤ 2 * Complex.normSq a + 2 * Complex.normSq b := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      have := norm_add_le a b
      nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b,
        norm_nonneg (a + b)]
    have hA : Complex.normSq a ≤ (κ : ℝ) * ∑ x ∈ T, Complex.normSq (v x j) :=
      cs_bound T (fun x => v x j) κ (by exact_mod_cast hT)
    have hB : Complex.normSq b ≤ B * ∑ x ∈ Tᶜ, Complex.normSq (v x j) := by
      refine cs_bound (Tᶜ) (fun x => v x j) B ?_
      have : (Tᶜ).card ≤ Fintype.card ι := Finset.card_le_univ (Tᶜ)
      rw [hBdef]
      exact_mod_cast this
    rw [h1, hsplit]
    calc (B⁻¹) ^ 2 * Complex.normSq (a + b)
        ≤ (B⁻¹) ^ 2 * (2 * ((κ : ℝ) * ∑ x ∈ T, Complex.normSq (v x j)) +
            2 * (B * ∑ x ∈ Tᶜ, Complex.normSq (v x j))) := by
          gcongr
          linarith [hadd, hA, hB]
      _ = 2 * κ / B ^ 2 * ∑ x ∈ T, Complex.normSq (v x j) +
            2 / B * ∑ x ∈ Tᶜ, Complex.normSq (v x j) := by
          field_simp <;> ring
  have e1 : ∑ j, ∑ x ∈ T, Complex.normSq (v x j) = ∑ x ∈ T, nsq (v x) := Finset.sum_comm
  have e2 : ∑ j, ∑ x ∈ Tᶜ, Complex.normSq (v x j) = ∑ x ∈ Tᶜ, nsq (v x) := Finset.sum_comm
  calc nsq (meanS v) = ∑ j, Complex.normSq (meanS v j) := rfl
    _ ≤ ∑ j, (2 * κ / B ^ 2 * ∑ x ∈ T, Complex.normSq (v x j) +
        2 / B * ∑ x ∈ Tᶜ, Complex.normSq (v x j)) :=
        Finset.sum_le_sum fun j _ => key j
    _ = 2 * κ / B ^ 2 * ∑ x ∈ T, nsq (v x) +
        2 / B * ∑ x ∈ Tᶜ, nsq (v x) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, e1, e2]

/-- The success weight of run `i` on the branches of `E`: live branches whose store is good for
`i`. -/
noncomputable def succG {Var ι : Type} {Q : ℕ} (good : Store Var → ι → Prop)
    [∀ σ i, Decidable (good σ i)] (i : ι) (E : List (Branch Var ι Q)) : ℝ :=
  ((E.filter fun β ↦ β.live && decide (good β.store i)).map fun β ↦ nsq (β.vec i)).sum

private lemma list_sum_lin' {α : Type} (E : List α) (a m : α → ℝ) (c₁ c₂ : ℝ) :
    (E.map fun β ↦ c₁ * a β + c₂ * (m β - a β)).sum =
      c₁ * (E.map a).sum + c₂ * ((E.map m).sum - (E.map a).sum) := by
  induction E with
  | nil => simp
  | cons β E ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

private lemma list_mul' {α : Type} (E : List α) (f : α → ℝ) (c : ℝ) :
    c * (E.map f).sum = (E.map fun a ↦ c * f a).sum := by
  induction E with
  | nil => simp
  | cons b E ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, ih]

/-- The summed end bound. -/
theorem sum_meanS_le {Var ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {Q : ℕ}
    (good : Store Var → ι → Prop) [∀ σ i, Decidable (good σ i)]
    (κ : ℕ) (hκ : ∀ σ, (Finset.univ.filter (good σ)).card ≤ κ)
    (E : List (Branch Var ι Q)) (hmass : ∀ i, (E.map fun β ↦ nsq (β.vec i)).sum ≤ 1) :
    (E.map fun β ↦ nsq (meanS β.vec)).sum ≤
      2 * κ / (Fintype.card ι : ℝ) + 2 / (Fintype.card ι : ℝ) * ∑ i, (1 - succG good i E) := by
  have hBpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  set B : ℝ := (Fintype.card ι : ℝ) with hBdef
  -- the branchwise quantities
  let g : ι → Branch Var ι Q → ℝ := fun x β ↦
    if (β.live && decide (good β.store x)) = true then nsq (β.vec x) else 0
  let Tb : Branch Var ι Q → Finset ι := fun β ↦
    Finset.univ.filter fun x ↦ (β.live && decide (good β.store x)) = true
  have hTb : ∀ β, (Tb β).card ≤ κ := by
    intro β
    refine le_trans (Finset.card_le_card ?_) (hκ β.store)
    intro x hx
    simp only [Tb, Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
      decide_eq_true_eq] at hx ⊢
    exact hx.2
  have hTsum : ∀ β, ∑ x ∈ Tb β, nsq (β.vec x) = ∑ x, g x β := by
    intro β
    simp only [Tb, g]
    rw [Finset.sum_filter]
  have hbeta : ∀ β : Branch Var ι Q, nsq (meanS β.vec) ≤
      2 * κ / B ^ 2 * ∑ x, g x β + 2 / B * ((∑ x, nsq (β.vec x)) - ∑ x, g x β) := by
    intro β
    have h := nsq_meanS_split β.vec (Tb β) κ (hTb β)
    have hc := Finset.sum_compl_add_sum (Tb β) (fun x ↦ nsq (β.vec x))
    rw [hTsum β] at h hc
    have : ∑ x ∈ (Tb β)ᶜ, nsq (β.vec x) = (∑ x, nsq (β.vec x)) - ∑ x, g x β := by linarith
    rw [this] at h
    exact h
  have hsum1 : (E.map fun β ↦ nsq (meanS β.vec)).sum ≤
      (E.map fun β ↦ 2 * κ / B ^ 2 * ∑ x, g x β +
        2 / B * ((∑ x, nsq (β.vec x)) - ∑ x, g x β)).sum :=
    List.sum_le_sum fun β _ => hbeta β
  rw [list_sum_lin'] at hsum1
  have hA : (E.map fun β ↦ ∑ x, g x β).sum = ∑ x, succG good x E := by
    rw [← finset_sum_list_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold succG
    rw [sum_filter_ite]
  have hM : (E.map fun β ↦ ∑ x, nsq (β.vec x)).sum =
      ∑ x, (E.map fun β ↦ nsq (β.vec x)).sum := (finset_sum_list_sum E _).symm
  have hsx : ∀ x, succG good x E ≤ 1 := by
    intro x
    refine le_trans ?_ (hmass x)
    unfold succG
    rw [sum_filter_ite]
    refine List.sum_le_sum fun β _ => ?_
    split_ifs
    · exact le_rfl
    · exact nsq_nonneg _
  have hAle : ∑ x, succG good x E ≤ B := by
    calc ∑ x, succG good x E ≤ ∑ _x : ι, (1 : ℝ) := Finset.sum_le_sum fun x _ => hsx x
      _ = B := by simp [hBdef]
  have hMle : (E.map fun β ↦ ∑ x, nsq (β.vec x)).sum ≤ B := by
    rw [hM]
    calc _ ≤ ∑ _x : ι, (1 : ℝ) := Finset.sum_le_sum fun x _ => hmass x
      _ = B := by simp [hBdef]
  rw [hA, hM] at hsum1
  rw [hM] at hMle
  have hR : ∑ x, (1 - succG good x E) = B - ∑ x, succG good x E := by
    rw [Finset.sum_sub_distrib]
    simp [hBdef]
  rw [hR]
  set A := ∑ x, succG good x E with hAdef
  set M := ∑ x, (E.map fun β ↦ nsq (β.vec x)).sum with hMdef
  have hκ0 : (0 : ℝ) ≤ 2 * κ / B ^ 2 := by positivity
  have e1 : 2 * κ / B ^ 2 * A ≤ 2 * κ / B := by
    have h1 : 2 * κ / B ^ 2 * A ≤ 2 * κ / B ^ 2 * B :=
      mul_le_mul_of_nonneg_left hAle hκ0
    have h2 : 2 * κ / B ^ 2 * B = 2 * κ / B := by field_simp
    linarith
  have e2 : 2 / B * (M - A) ≤ 2 / B * (B - A) := by
    have : 0 ≤ 2 / B := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) this
  linarith

/-- The all-branch cost weights of all runs sum to `card ι` times the average-weighted count. -/
theorem cwaS_sum {Var ι : Type} [Fintype ι] [Nonempty ι] {Q : ℕ} (E : List (Branch Var ι Q)) :
    ∑ i, GroverThreeFifths.cwa i E = (Fintype.card ι : ℝ) * (E.map fun β ↦ (β.count : ℝ) * avgS β.vec).sum := by
  unfold GroverThreeFifths.cwa
  rw [finset_sum_list_sum, list_mul']
  congr 1
  refine List.map_congr_left fun β _ => ?_
  have hN : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [← Finset.mul_sum]
  unfold avgS
  field_simp

end GroverParallel

#print axioms GroverParallel.nsq_meanS_split
#print axioms GroverParallel.sum_meanS_le
#print axioms GroverParallel.cwaS_sum
