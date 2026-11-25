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
import LowerBounds.Grover.FindAllOracle
import LowerBounds.Grover.ParallelBound
import LowerBounds.Grover.ParallelCost
import Mathlib

/-!
# The end bound for the matrix potential

`end_gramY_le`: for a coefficient matrix with non-positive diagonal and entries bounded by `Ymax`,
and branches whose store is good for at most one run index, the final `gramY` summed over the
branches is at most `Ymax * card ι * (2 √F + F)`, where `F` is the total failure probability.
-/

open QuantumComputation.Specs Operator ResourceCounting Filter Real
open scoped Matrix QHLExpectation ComplexOrder MatrixOrder ENNReal NNReal
open QuantumComputation.Specs.Grover (Var)
open QuantumComputation.Specs.Grover.Var (res)

namespace GroverParallel

open GroverLowerBound

/-! ### Scalar and list helpers -/

private lemma ipRe_selfF {d : ℕ} (a : Fin d → ℂ) : (∑ j, star (a j) * a j).re = nsq a := by
  simp [nsq, Complex.re_sum, Complex.normSq_apply]

/-- Cauchy-Schwarz for the real part of the inner product. -/
private lemma ipRe_abs_le {d : ℕ} (a b : Fin d → ℂ) :
    |(∑ j, star (a j) * b j).re| ≤ √(nsq a) * √(nsq b) := by
  have h1 : |(∑ j, star (a j) * b j).re| ≤ ∑ j, ‖a j‖ * ‖b j‖ := by
    calc |(∑ j, star (a j) * b j).re| ≤ ‖∑ j, star (a j) * b j‖ := Complex.abs_re_le_norm _
      _ ≤ ∑ j, ‖star (a j) * b j‖ := norm_sum_le _ _
      _ = ∑ j, ‖a j‖ * ‖b j‖ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, norm_star]
  have h2 : (∑ j, ‖a j‖ * ‖b j‖) ^ 2 ≤ (∑ j, ‖a j‖ ^ 2) * ∑ j, ‖b j‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have ha : nsq a = ∑ j, ‖a j‖ ^ 2 := by
    unfold nsq
    exact Finset.sum_congr rfl fun j _ => Complex.normSq_eq_norm_sq _
  have hb : nsq b = ∑ j, ‖b j‖ ^ 2 := by
    unfold nsq
    exact Finset.sum_congr rfl fun j _ => Complex.normSq_eq_norm_sq _
  rw [← Real.sqrt_mul (nsq_nonneg a) (nsq b)]
  refine le_trans h1 (Real.le_sqrt_of_sq_le ?_)
  rw [ha, hb]
  exact h2

private lemma list_add {α : Type} (E : List α) (f g : α → ℝ) :
    (E.map fun a ↦ f a + g a).sum = (E.map f).sum + (E.map g).sum := by
  induction E with
  | nil => simp
  | cons b E ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

private lemma list_mul_left {α : Type} (E : List α) (f : α → ℝ) (c : ℝ) :
    (E.map fun a ↦ c * f a).sum = c * (E.map f).sum := by
  induction E with
  | nil => simp
  | cons b E ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]

private lemma list_lin2 {α : Type} (E : List α) (f g : α → ℝ) (c d : ℝ) :
    (E.map fun a ↦ c * f a + d * g a).sum = c * (E.map f).sum + d * (E.map g).sum := by
  induction E with
  | nil => simp
  | cons b E ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

private lemma amgm_aux (t X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) (h : t ^ 2 ≤ X * Y) :
    2 * t ≤ X + Y := by
  by_contra hc
  push_neg at hc
  nlinarith [mul_pos (sub_pos.2 hc) (by linarith : 0 < 2 * t + (X + Y)), sq_nonneg (X - Y)]

/-- Cauchy-Schwarz for list sums. -/
private lemma list_cs {α : Type} (L : List α) (f g : α → ℝ) :
    (L.map fun a ↦ f a * g a).sum ^ 2 ≤
      (L.map fun a ↦ f a ^ 2).sum * (L.map fun a ↦ g a ^ 2).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    have hP : 0 ≤ (L.map fun a ↦ f a ^ 2).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨b, _, rfl⟩ := List.mem_map.1 hx
        exact sq_nonneg _
    have hR : 0 ≤ (L.map fun a ↦ g a ^ 2).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨b, _, rfl⟩ := List.mem_map.1 hx
        exact sq_nonneg _
    have key := amgm_aux ((L.map fun a ↦ f a * g a).sum * (f a * g a))
      ((L.map fun a ↦ f a ^ 2).sum * g a ^ 2) (f a ^ 2 * (L.map fun a ↦ g a ^ 2).sum)
      (mul_nonneg hP (sq_nonneg _)) (mul_nonneg (sq_nonneg _) hR)
      (by
        calc ((L.map fun a ↦ f a * g a).sum * (f a * g a)) ^ 2
            = (L.map fun a ↦ f a * g a).sum ^ 2 * (f a ^ 2 * g a ^ 2) := by ring
          _ ≤ ((L.map fun a ↦ f a ^ 2).sum * (L.map fun a ↦ g a ^ 2).sum) *
                (f a ^ 2 * g a ^ 2) :=
              mul_le_mul_of_nonneg_right ih (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          _ = ((L.map fun a ↦ f a ^ 2).sum * g a ^ 2) *
                (f a ^ 2 * (L.map fun a ↦ g a ^ 2).sum) := by ring)
    nlinarith [ih, key]

/-! ### One branch -/

private lemma branch_bound {ι : Type} [Fintype ι] {Q : ℕ} (Y : ι → ι → ℝ)
    (hdiag : ∀ S, Y S S ≤ 0) (Ymax : ℝ) (hYmax : ∀ S S', |Y S S'| ≤ Ymax)
    (p : ι → Prop) [DecidablePred p] (hp : (Finset.univ.filter p).card ≤ 1)
    (v : ι → Fin (2 ^ Q) → ℂ) (w gg bb : ι → ℝ) (hw : ∀ S, w S = √(nsq (v S)))
    (hgg : ∀ S, gg S = if p S then w S else 0) (hbb : ∀ S, bb S = if p S then 0 else w S) :
    gramY Y v ≤ Ymax * (2 * (∑ S, gg S) * (∑ S, bb S) + (∑ S, bb S) ^ 2) := by
  have hterm : ∀ S S', Y S S' * (∑ j, star (v S j) * v S' j).re ≤
      Ymax * (w S * w S') - Ymax * (gg S * gg S') := by
    intro S S'
    by_cases h : p S ∧ p S'
    · have hSS : S = S' := by
        rw [Finset.card_le_one] at hp
        exact hp S (by simpa using h.1) S' (by simpa using h.2)
      have e1 : gg S = w S := by rw [hgg S, if_pos h.1]
      have e2 : gg S' = w S' := by rw [hgg S', if_pos h.2]
      have hip : (∑ j, star (v S j) * v S' j).re = nsq (v S) := by
        rw [← hSS]
        exact ipRe_selfF _
      have hneg : Y S S * nsq (v S) ≤ 0 :=
        mul_nonpos_iff.2 (Or.inr ⟨hdiag S, nsq_nonneg _⟩)
      rw [hip, e1, e2, ← hSS]
      linarith
    · have hz : gg S * gg S' = 0 := by
        by_cases h1 : p S
        · have h2 : ¬ p S' := fun h2 => h ⟨h1, h2⟩
          rw [hgg S', if_neg h2, mul_zero]
        · rw [hgg S, if_neg h1, zero_mul]
      rw [hz, mul_zero, sub_zero]
      have hS := hYmax S S'
      have hi : |(∑ j, star (v S j) * v S' j).re| ≤ w S * w S' := by
        rw [hw S, hw S']
        exact ipRe_abs_le (v S) (v S')
      calc Y S S' * (∑ j, star (v S j) * v S' j).re
          ≤ |Y S S' * (∑ j, star (v S j) * v S' j).re| := le_abs_self _
        _ = |Y S S'| * |(∑ j, star (v S j) * v S' j).re| := abs_mul _ _
        _ ≤ Ymax * (w S * w S') :=
            mul_le_mul hS hi (abs_nonneg _) (le_trans (abs_nonneg _) hS)
  have hsplit : ∀ S, w S = gg S + bb S := fun S => by
    rw [hgg S, hbb S]
    by_cases h : p S <;> simp [h]
  have hW : ∑ S, w S = ∑ S, gg S + ∑ S, bb S := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun S _ => hsplit S
  unfold gramY
  calc ∑ S, ∑ S', Y S S' * (∑ j, star (v S j) * v S' j).re
      ≤ ∑ S, ∑ S', (Ymax * (w S * w S') - Ymax * (gg S * gg S')) :=
        Finset.sum_le_sum fun S _ => Finset.sum_le_sum fun S' _ => hterm S S'
    _ = Ymax * ((∑ S, w S) * (∑ S, w S)) - Ymax * ((∑ S, gg S) * (∑ S, gg S)) := by
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        try ring
    _ = Ymax * (2 * (∑ S, gg S) * (∑ S, bb S) + (∑ S, bb S) ^ 2) := by
        rw [hW]
        ring

private lemma branch_cs {ι : Type} [Fintype ι] {Q : ℕ} (p : ι → Prop) [DecidablePred p]
    (hp : (Finset.univ.filter p).card ≤ 1) (v : ι → Fin (2 ^ Q) → ℂ) (w gg bb : ι → ℝ)
    (hw : ∀ S, w S = √(nsq (v S)))
    (hgg : ∀ S, gg S = if p S then w S else 0) (hbb : ∀ S, bb S = if p S then 0 else w S) :
    0 ≤ ∑ S, gg S ∧ (∑ S, gg S) ^ 2 ≤ ∑ S, (if p S then nsq (v S) else 0) ∧
      0 ≤ ∑ S, bb S ∧
      (∑ S, bb S) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ S, (if p S then 0 else nsq (v S)) := by
  have hw2 : ∀ S, w S ^ 2 = nsq (v S) := fun S => by
    rw [hw S, Real.sq_sqrt (nsq_nonneg _)]
  have hw0 : ∀ S, 0 ≤ w S := fun S => by
    rw [hw S]
    exact Real.sqrt_nonneg _
  have hg : ∑ S, gg S = ∑ S ∈ Finset.univ.filter p, w S := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun S _ => hgg S
  have hb : ∑ S, bb S = ∑ S ∈ Finset.univ.filter (fun S => ¬ p S), w S := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [hbb S]
    by_cases h : p S <;> simp [h]
  have hg2 : ∑ S ∈ Finset.univ.filter p, w S ^ 2 = ∑ S, (if p S then nsq (v S) else 0) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun S _ => by rw [hw2 S]
  have hb2 : ∑ S ∈ Finset.univ.filter (fun S => ¬ p S), w S ^ 2 =
      ∑ S, (if p S then 0 else nsq (v S)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [hw2 S]
    by_cases h : p S <;> simp [h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Finset.sum_nonneg fun S _ => by
      rw [hgg S]
      split_ifs
      exacts [hw0 S, le_rfl]
  · have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.univ.filter p) (f := w)
    have hc : ((Finset.univ.filter p).card : ℝ) ≤ 1 := by exact_mod_cast hp
    have h2 : 0 ≤ ∑ S ∈ Finset.univ.filter p, w S ^ 2 :=
      Finset.sum_nonneg fun S _ => sq_nonneg _
    rw [hg, ← hg2]
    nlinarith [mul_nonneg (sub_nonneg.2 hc) h2]
  · exact Finset.sum_nonneg fun S _ => by
      rw [hbb S]
      split_ifs
      exacts [le_rfl, hw0 S]
  · have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.univ.filter (fun S => ¬ p S)) (f := w)
    have hc : ((Finset.univ.filter (fun S => ¬ p S)).card : ℝ) ≤ (Fintype.card ι : ℝ) := by
      exact_mod_cast Finset.card_le_univ _
    have h2 : 0 ≤ ∑ S ∈ Finset.univ.filter (fun S => ¬ p S), w S ^ 2 :=
      Finset.sum_nonneg fun S _ => sq_nonneg _
    rw [hb, ← hb2]
    nlinarith [mul_nonneg (sub_nonneg.2 hc) h2]

/-! ### The end bound -/

/-- end bound: branches whose store is good for at most one run index -/
theorem end_gramY_le {Var ι : Type} [Fintype ι] {Q : ℕ} (Y : ι → ι → ℝ) (hdiag : ∀ S, Y S S ≤ 0)
    (Ymax : ℝ) (hYmax : ∀ S S', |Y S S'| ≤ Ymax)
    (good : Store Var → ι → Prop) [∀ σ S, Decidable (good σ S)]
    (hgood : ∀ σ, (Finset.univ.filter (good σ)).card ≤ 1)
    (E : List (Branch Var ι Q)) (hmass : ∀ S, (E.map fun β ↦ nsq (β.vec S)).sum ≤ 1) :
    (E.map fun β ↦ gramY Y β.vec).sum ≤
      Ymax * (Fintype.card ι : ℝ) *
        (2 * √(∑ S, (1 - succG good S E)) + ∑ S, (1 - succG good S E)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h0 : ∀ β : Branch Var ι Q, gramY Y β.vec = 0 := fun β => by simp [gramY]
    have h1 : (E.map fun β ↦ gramY Y β.vec) = E.map fun _ ↦ (0 : ℝ) :=
      List.map_congr_left fun β _ => h0 β
    rw [h1]
    simp
  have hYm0 : 0 ≤ Ymax := by
    obtain ⟨S⟩ := hι
    exact le_trans (abs_nonneg _) (hYmax S S)
  have hB0 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  generalize hε : ∑ S, (1 - succG good S E) = ε
  -- the good set of a branch has at most one element
  have hp : ∀ β : Branch Var ι Q,
      (Finset.univ.filter fun S => (β.live && decide (good β.store S)) = true).card ≤ 1 := by
    intro β
    refine le_trans (Finset.card_le_card ?_) (hgood β.store)
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
      decide_eq_true_eq] at hx ⊢
    exact hx.2
  -- branchwise quantities
  obtain ⟨gw, hgw⟩ : ∃ gw : Branch Var ι Q → ℝ, ∀ β, gw β =
      ∑ S, if (β.live && decide (good β.store S)) = true then √(nsq (β.vec S)) else 0 :=
    ⟨fun β => ∑ S, if (β.live && decide (good β.store S)) = true then √(nsq (β.vec S)) else 0,
      fun _ => rfl⟩
  obtain ⟨bw, hbw⟩ : ∃ bw : Branch Var ι Q → ℝ, ∀ β, bw β =
      ∑ S, if (β.live && decide (good β.store S)) = true then 0 else √(nsq (β.vec S)) :=
    ⟨fun β => ∑ S, if (β.live && decide (good β.store S)) = true then 0 else √(nsq (β.vec S)),
      fun _ => rfl⟩
  obtain ⟨Gm, hgm⟩ : ∃ Gm : Branch Var ι Q → ℝ, ∀ β, Gm β =
      ∑ S, if (β.live && decide (good β.store S)) = true then nsq (β.vec S) else 0 :=
    ⟨fun β => ∑ S, if (β.live && decide (good β.store S)) = true then nsq (β.vec S) else 0,
      fun _ => rfl⟩
  obtain ⟨Rm, hrm⟩ : ∃ Rm : Branch Var ι Q → ℝ, ∀ β, Rm β =
      ∑ S, if (β.live && decide (good β.store S)) = true then 0 else nsq (β.vec S) :=
    ⟨fun β => ∑ S, if (β.live && decide (good β.store S)) = true then 0 else nsq (β.vec S),
      fun _ => rfl⟩
  have hb1 : ∀ β : Branch Var ι Q,
      gramY Y β.vec ≤ Ymax * (2 * gw β * bw β + bw β ^ 2) := by
    intro β
    rw [hgw β, hbw β]
    exact branch_bound Y hdiag Ymax hYmax
      (fun S => (β.live && decide (good β.store S)) = true) (hp β) β.vec
      (fun S => √(nsq (β.vec S)))
      (fun S => if (β.live && decide (good β.store S)) = true then √(nsq (β.vec S)) else 0)
      (fun S => if (β.live && decide (good β.store S)) = true then 0 else √(nsq (β.vec S)))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have hcs : ∀ β : Branch Var ι Q, 0 ≤ gw β ∧ gw β ^ 2 ≤ Gm β ∧ 0 ≤ bw β ∧
      bw β ^ 2 ≤ (Fintype.card ι : ℝ) * Rm β := by
    intro β
    rw [hgw β, hbw β, hgm β, hrm β]
    exact branch_cs (fun S => (β.live && decide (good β.store S)) = true) (hp β) β.vec
      (fun S => √(nsq (β.vec S)))
      (fun S => if (β.live && decide (good β.store S)) = true then √(nsq (β.vec S)) else 0)
      (fun S => if (β.live && decide (good β.store S)) = true then 0 else √(nsq (β.vec S)))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  -- the good mass over the branches is the success weight
  have hGsum : (E.map Gm).sum = ∑ S, succG good S E := by
    have e1 : E.map Gm = E.map fun β =>
        ∑ S, if (β.live && decide (good β.store S)) = true then nsq (β.vec S) else 0 :=
      List.map_congr_left fun β _ => hgm β
    have e2 := finset_sum_list_sum E (fun (S : ι) (β : Branch Var ι Q) =>
      if (β.live && decide (good β.store S)) = true then nsq (β.vec S) else 0)
    rw [e1, ← e2]
    refine Finset.sum_congr rfl fun S _ => ?_
    unfold succG
    rw [sum_filter_ite]
  have hGR : ∀ β : Branch Var ι Q, Gm β + Rm β = ∑ S, nsq (β.vec S) := by
    intro β
    rw [hgm β, hrm β, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    split_ifs <;> simp
  have hMsum : (E.map fun β ↦ ∑ S, nsq (β.vec S)).sum =
      ∑ S, (E.map fun β ↦ nsq (β.vec S)).sum := (finset_sum_list_sum E _).symm
  have hMle : ∑ S, (E.map fun β ↦ nsq (β.vec S)).sum ≤ (Fintype.card ι : ℝ) := by
    calc _ ≤ ∑ _S : ι, (1 : ℝ) := Finset.sum_le_sum fun S _ => hmass S
      _ = _ := by simp
  have hsplit : (E.map Gm).sum + (E.map Rm).sum = (E.map fun β ↦ ∑ S, nsq (β.vec S)).sum := by
    rw [← list_add]
    exact congrArg List.sum (List.map_congr_left fun β _ => hGR β)
  have hsx : ∀ S, succG good S E ≤ 1 := by
    intro S
    refine le_trans ?_ (hmass S)
    unfold succG
    rw [sum_filter_ite]
    refine List.sum_le_sum fun β _ => ?_
    split_ifs
    · exact le_rfl
    · exact nsq_nonneg _
  have hε0 : 0 ≤ ε := by
    rw [← hε]
    exact Finset.sum_nonneg fun S _ => by linarith [hsx S]
  have hεA : ε = (Fintype.card ι : ℝ) - ∑ S, succG good S E := by
    rw [← hε, Finset.sum_sub_distrib]
    simp
  have hRle : (E.map Rm).sum ≤ ε := by linarith
  have hG2 : (E.map fun β ↦ gw β ^ 2).sum ≤ (Fintype.card ι : ℝ) := by
    have : (E.map fun β ↦ gw β ^ 2).sum ≤ (E.map Gm).sum :=
      List.sum_le_sum fun β _ => (hcs β).2.1
    linarith
  have hb2 : (E.map fun β ↦ bw β ^ 2).sum ≤ (Fintype.card ι : ℝ) * ε := by
    calc (E.map fun β ↦ bw β ^ 2).sum
        ≤ (E.map fun β ↦ (Fintype.card ι : ℝ) * Rm β).sum :=
          List.sum_le_sum fun β _ => (hcs β).2.2.2
      _ = (Fintype.card ι : ℝ) * (E.map Rm).sum := list_mul_left E Rm _
      _ ≤ (Fintype.card ι : ℝ) * ε := mul_le_mul_of_nonneg_left hRle hB0
  have hRnn : 0 ≤ (E.map fun β ↦ bw β ^ 2).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨b, _, rfl⟩ := List.mem_map.1 hx
      exact sq_nonneg _
  have hcs2 := list_cs E gw bw
  have hX2 : (E.map fun β ↦ gw β * bw β).sum ^ 2 ≤
      (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) * ε) :=
    le_trans hcs2 (mul_le_mul hG2 hb2 hRnn hB0)
  have hX : (E.map fun β ↦ gw β * bw β).sum ≤ (Fintype.card ι : ℝ) * √ε := by
    by_contra hc
    push_neg at hc
    have hc0 : 0 ≤ (Fintype.card ι : ℝ) * √ε := mul_nonneg hB0 (Real.sqrt_nonneg _)
    have h1 := mul_self_lt_mul_self hc0 hc
    have h2 : ((Fintype.card ι : ℝ) * √ε) * ((Fintype.card ι : ℝ) * √ε) =
        (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) * ε) := by
      have := Real.mul_self_sqrt hε0
      calc ((Fintype.card ι : ℝ) * √ε) * ((Fintype.card ι : ℝ) * √ε)
          = (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ) * (√ε * √ε) := by ring
        _ = _ := by rw [this]; ring
    nlinarith
  have hmain : (E.map fun β ↦ gramY Y β.vec).sum ≤
      Ymax * (2 * (E.map fun β ↦ gw β * bw β).sum + (E.map fun β ↦ bw β ^ 2).sum) := by
    calc (E.map fun β ↦ gramY Y β.vec).sum
        ≤ (E.map fun β ↦ Ymax * (2 * gw β * bw β + bw β ^ 2)).sum :=
          List.sum_le_sum fun β _ => hb1 β
      _ = (E.map fun β ↦ (2 * Ymax) * (gw β * bw β) + Ymax * (bw β ^ 2)).sum :=
          congrArg List.sum (List.map_congr_left fun β _ => by ring)
      _ = Ymax * (2 * (E.map fun β ↦ gw β * bw β).sum + (E.map fun β ↦ bw β ^ 2).sum) := by
          rw [list_lin2]
          ring
  have hfin : Ymax * (2 * (E.map fun β ↦ gw β * bw β).sum + (E.map fun β ↦ bw β ^ 2).sum) ≤
      Ymax * (2 * ((Fintype.card ι : ℝ) * √ε) + (Fintype.card ι : ℝ) * ε) :=
    mul_le_mul_of_nonneg_left (by linarith) hYm0
  have e : Ymax * (2 * ((Fintype.card ι : ℝ) * √ε) + (Fintype.card ι : ℝ) * ε) =
      Ymax * (Fintype.card ι : ℝ) * (2 * √ε + ε) := by ring
  rw [e] at hfin
  exact le_trans hmain hfin

end GroverParallel

#print axioms GroverParallel.end_gramY_le
