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
import LowerBounds.Grover.Link
import LowerBounds.Grover.Hybrid
import LowerBounds.Grover.Mean
import Mathlib

/-!
# All-branch cost, total mass and the end bound

* `cwa`, `rep_cost_all`: the oracle-count weight over *all* branches (aborted ones keep their past
  oracle calls), bounded by the library's expected oracle cost exactly as
  `GroverLowerBound.rep_cost`.
* `mass_ens_le`: the total squared norm of one run never grows along `ens`.
* `nsq_meanV_split`: per branch, the squared norm of the mean of the run vectors.
* `sum_meanV_le`: summed over the branches of a list.
-/

open QuantumComputation.Specs Operator ResourceCounting GroverLowerBound
open scoped Matrix QHLExpectation ComplexOrder MatrixOrder

namespace GroverThreeFifths

/-! ### All-branch cost weight -/

/-- The oracle-count weight over all branches, live or not. -/
noncomputable def cwa {Var ι : Type} {Q : ℕ} (i₀ : ι) (E : List (Branch Var ι Q)) : ℝ :=
  (E.map fun β ↦ (β.count : ℝ) * nsq (β.vec i₀)).sum

section cost

variable {Var : Type} [DecidableEq Var] {ι : Type} {Q w : ℕ} (i₀ : ι)

lemma cwa_append (E F : List (Branch Var ι Q)) : cwa i₀ (E ++ F) = cwa i₀ E + cwa i₀ F := by
  simp [cwa]

lemma cwa_split (b : Store Var → Prop) [DecidablePred b] (E : List (Branch Var ι Q)) :
    cwa i₀ E = cwa i₀ (E.filter fun β => decide (b β.store)) +
      cwa i₀ (E.filter fun β => !decide (b β.store)) :=
  (sum_filter_split (fun β : Branch Var ι Q => decide (b β.store))
    (fun β ↦ (β.count : ℝ) * nsq (β.vec i₀)) E).symm

lemma cwa_ens_abort (G : ι → ℕ → QRegister w Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (E : List (Branch Var ι Q)) : cwa i₀ (ens G (.abort : LF Var Q w) E) = cwa i₀ E := by
  simp [cwa, ens, List.map_map, Function.comp_def]

lemma cwa_ens_step (G : ι → ℕ → QRegister w Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (U : Unitary (2 ^ Q)) (E : List (Branch Var ι Q)) :
    cwa i₀ (ens G (.step U : LF Var Q w) E) = cwa i₀ E := by
  simp only [cwa, ens, List.map_map]
  congr 1
  refine List.map_congr_left fun β _ => ?_
  by_cases h : β.live
  · simp [h, nsq_unitary]
  · simp [h]

lemma cwa_ens_oracle (O : Unitary (2 ^ w))
    (G : ι → ℕ → QRegister w Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (hG : ∀ k r, G i₀ k r = (r.embedUnitary O).1) (r : QRegister w Q)
    (E : List (Branch Var ι Q)) :
    cwa i₀ (ens G (.oracle r : LF Var Q w) E) =
      cwa i₀ E + ((E.filter (·.live)).map fun β ↦ nsq (β.vec i₀)).sum := by
  rw [filter_live_sum]
  unfold cwa
  rw [← List.sum_map_add]
  simp only [ens, List.map_map]
  congr 1
  refine List.map_congr_left fun β _ => ?_
  by_cases h : β.live
  · have hn : nsq (r.embedMatrix O.1 *ᵥ β.vec i₀) = nsq (β.vec i₀) :=
      nsq_unitary (r.embedUnitary O) _
    simp [h, hG, hn]
    ring
  · simp [h]

lemma cwa_ens_measure {k : ℕ}
    (G : ι → ℕ → QRegister w Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (v : Var) (r : QRegister k Q) (E : List (Branch Var ι Q)) :
    cwa i₀ (ens G (.measure v r : LF Var Q w) E) = cwa i₀ E := by
  simp only [cwa, ens, lsum_flatMap]
  congr 1
  refine List.map_congr_left fun β _ => ?_
  by_cases h : β.live
  · rw [if_pos h, sum_finRange_map]
    dsimp only
    rw [← Finset.mul_sum, sum_nsq_measure]
  · simp [h]

variable {i₀}

/-- The all-branch version of `GroverLowerBound.rep_cost`. -/
theorem rep_cost_all {Δ : CQState (Store Var) (2 ^ Q)} {E : List (Branch Var ι Q)}
    (O : Unitary (2 ^ w)) (G : ι → ℕ → QRegister w Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (hG : ∀ k r, G i₀ k r = (r.embedUnitary O).1) (P : LF Var Q w) :
    Rep Δ E i₀ →
      ENNReal.ofReal (cwa i₀ (ens G P E) - cwa i₀ E) ≤
        expectedCost (CostModel.ofEmbeddedOracle O) (P.compile O) Δ := by
  induction P generalizing Δ E with
  | skip => intro _; simp [ens]
  | abort =>
    intro _
    rw [cwa_ens_abort, sub_self]
    simp
  | step U =>
    intro _
    rw [cwa_ens_step]
    simp
  | oracle r =>
    intro h
    rw [cwa_ens_oracle i₀ O G hG, add_sub_cancel_left, ← rep_trace h]
    simp [LF.compile, expectedCost]
  | measure v r =>
    intro _
    rw [cwa_ens_measure]
    simp
  | qIf b t f iht ihf =>
    intro h
    simp only [LF.compile, expectedCost, ens]
    have hs := cwa_split i₀ b E
    have h1 := iht (rep_restrict b h)
    have h2 : Rep (Δ.restrict (¬ b ·)) (E.filter fun β => !decide (b β.store)) i₀ := by
      have := rep_restrict (fun σ => ¬ b σ) h
      simpa [decide_not] using this
    have h3 := ihf h2
    rw [cwa_append, hs]
    have e : ∀ a b c d : ℝ, a + b - (c + d) = (a - c) + (b - d) := fun a b c d => by ring
    rw [e]
    exact ENNReal.ofReal_add_le.trans (add_le_add h1 h3)
  | seq p₁ p₂ ih₁ ih₂ =>
    intro h
    simp only [LF.compile, expectedCost, ens]
    have h1 := ih₁ h
    have h2 := ih₂ (rep_interp O G hG p₁ h)
    calc ENNReal.ofReal (cwa i₀ (ens G p₂ (ens G p₁ E)) - cwa i₀ E)
        = ENNReal.ofReal ((cwa i₀ (ens G p₂ (ens G p₁ E)) - cwa i₀ (ens G p₁ E)) +
            (cwa i₀ (ens G p₁ E) - cwa i₀ E)) := by congr 1; ring
      _ ≤ ENNReal.ofReal (cwa i₀ (ens G p₂ (ens G p₁ E)) - cwa i₀ (ens G p₁ E)) +
            ENNReal.ofReal (cwa i₀ (ens G p₁ E) - cwa i₀ E) := ENNReal.ofReal_add_le
      _ ≤ _ := by
          rw [add_comm]
          exact add_le_add h1 h2

/-! ### Total mass -/

/-- The total squared norm of run `i` never grows along `ens`, if every oracle matrix preserves
the norm. -/
theorem mass_ens_le (G : ι → ℕ → QRegister w Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (hG : ∀ i k r v, nsq (G i k r *ᵥ v) = nsq v) (P : LF Var Q w)
    (E : List (Branch Var ι Q)) (i : ι) :
    ((ens G P E).map fun β ↦ nsq (β.vec i)).sum ≤ (E.map fun β ↦ nsq (β.vec i)).sum := by
  have h := ens_sum_mono G (fun _ : Branch Var ι Q => True) (fun β => -nsq (β.vec i))
    (fun _ _ _ _ _ => trivial) (fun β _ => le_rfl)
    (fun U β _ => by
      by_cases h : β.live
      · simp [h, nsq_unitary]
      · simp [h])
    (fun r β _ => by
      by_cases h : β.live
      · simp [h, hG]
      · simp [h])
    (fun {k} v r β _ => by
      by_cases h : β.live
      · rw [if_pos h, sum_finRange_map]
        dsimp only
        rw [Finset.sum_neg_distrib, sum_nsq_measure]
      · rw [if_neg h]
        simp)
    P E (fun _ _ => trivial)
  simp only [sum_map_neg'] at h
  linarith

end cost

/-! ### The end bound -/

/-- Cauchy-Schwarz and the splitting of the mean, coordinatewise and then summed. -/
theorem nsq_meanV_split {n Q : ℕ} (v : Fin (2 ^ n) → Fin (2 ^ Q) → ℂ)
    (T : Finset (Fin (2 ^ n))) (hT : T.card ≤ 1) :
    nsq (meanV v) ≤ 2 / (2 ^ n : ℝ) ^ 2 * ∑ x ∈ T, nsq (v x) +
      2 / (2 ^ n : ℝ) * ∑ x ∈ Tᶜ, nsq (v x) := by
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have key : ∀ j, Complex.normSq (meanV v j) ≤
      2 / (2 ^ n : ℝ) ^ 2 * ∑ x ∈ T, Complex.normSq (v x j) +
        2 / (2 ^ n : ℝ) * ∑ x ∈ Tᶜ, Complex.normSq (v x j) := by
    intro j
    set N : ℝ := 2 ^ n with hNdef
    have hc : (((2 ^ n : ℕ) : ℂ))⁻¹ = (((N⁻¹ : ℝ)) : ℂ) := by
      rw [hNdef]; push_cast; rfl
    have h1 : Complex.normSq (meanV v j) = (N⁻¹) ^ 2 * Complex.normSq (∑ x, v x j) := by
      unfold meanV
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
    have hA : Complex.normSq a = ∑ x ∈ T, Complex.normSq (v x j) := by
      rw [Finset.card_le_one_iff_subsingleton_coe] at hT
      by_cases hne : T.Nonempty
      · obtain ⟨t, ht⟩ := hne
        have hTt : T = {t} := by
          refine Finset.eq_singleton_iff_unique_mem.2 ⟨ht, fun y hy => ?_⟩
          have := hT.elim ⟨y, hy⟩ ⟨t, ht⟩
          exact congrArg Subtype.val this
        rw [ha, hTt]
        simp
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [ha, hne]
        simp
    have hB : Complex.normSq b ≤ N * ∑ x ∈ Tᶜ, Complex.normSq (v x j) := by
      rw [Complex.normSq_eq_norm_sq]
      have h2 : ‖b‖ ≤ ∑ x ∈ Tᶜ, ‖v x j‖ := norm_sum_le _ _
      have h3 : ‖b‖ ^ 2 ≤ (∑ x ∈ Tᶜ, ‖v x j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h2 2
      have h4 := sq_sum_le_card_mul_sum_sq (s := Tᶜ) (f := fun x => ‖v x j‖)
      have h5 : ((Tᶜ).card : ℝ) ≤ N := by
        have : (Tᶜ).card ≤ 2 ^ n := by
          simpa using Finset.card_le_univ (Tᶜ)
        rw [hNdef]
        exact_mod_cast this
      have h6 : ∑ x ∈ Tᶜ, ‖v x j‖ ^ 2 = ∑ x ∈ Tᶜ, Complex.normSq (v x j) :=
        Finset.sum_congr rfl fun x _ => (Complex.normSq_eq_norm_sq _).symm
      have h7 : 0 ≤ ∑ x ∈ Tᶜ, ‖v x j‖ ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
      rw [h6] at h4 h7
      calc ‖b‖ ^ 2 ≤ _ := h3
        _ ≤ _ := h4
        _ ≤ N * ∑ x ∈ Tᶜ, Complex.normSq (v x j) := mul_le_mul_of_nonneg_right h5 h7
    rw [h1, hsplit]
    calc (N⁻¹) ^ 2 * Complex.normSq (a + b)
        ≤ (N⁻¹) ^ 2 * (2 * (∑ x ∈ T, Complex.normSq (v x j)) +
            2 * (N * ∑ x ∈ Tᶜ, Complex.normSq (v x j))) := by
          gcongr
          linarith [hadd, hA, hB]
      _ = 2 / N ^ 2 * ∑ x ∈ T, Complex.normSq (v x j) +
            2 / N * ∑ x ∈ Tᶜ, Complex.normSq (v x j) := by
          field_simp
  have e1 : ∑ j, ∑ x ∈ T, Complex.normSq (v x j) = ∑ x ∈ T, nsq (v x) := Finset.sum_comm
  have e2 : ∑ j, ∑ x ∈ Tᶜ, Complex.normSq (v x j) = ∑ x ∈ Tᶜ, nsq (v x) := Finset.sum_comm
  calc nsq (meanV v) = ∑ j, Complex.normSq (meanV v j) := rfl
    _ ≤ ∑ j, (2 / (2 ^ n : ℝ) ^ 2 * ∑ x ∈ T, Complex.normSq (v x j) +
        2 / (2 ^ n : ℝ) * ∑ x ∈ Tᶜ, Complex.normSq (v x j)) :=
        Finset.sum_le_sum fun j _ => key j
    _ = 2 / (2 ^ n : ℝ) ^ 2 * ∑ x ∈ T, nsq (v x) +
        2 / (2 ^ n : ℝ) * ∑ x ∈ Tᶜ, nsq (v x) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, e1, e2]

section summed

open QuantumComputation.Specs.Grover (Var)
open QuantumComputation.Specs.Grover.Var (res)

/-- The success weight of item `x` on the branches of `E`: live branches whose output is `x`. -/
noncomputable def succ {n Q : ℕ} (x : Fin (2 ^ n)) (E : List (Branch Var (Fin (2 ^ n)) Q)) : ℝ :=
  ((E.filter fun β ↦ β.live && decide (β.store res = (x.val : ℤ))).map
    fun β ↦ nsq (β.vec x)).sum

lemma list_sum_lin {α : Type} (E : List α) (a m : α → ℝ) (c₁ c₂ : ℝ) :
    (E.map fun β ↦ c₁ * a β + c₂ * (m β - a β)).sum =
      c₁ * (E.map a).sum + c₂ * ((E.map m).sum - (E.map a).sum) := by
  induction E with
  | nil => simp
  | cons β E ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

/-- The summed end bound. -/
theorem sum_meanV_le {n Q : ℕ} (E : List (Branch Var (Fin (2 ^ n)) Q))
    (hmass : ∀ x, (E.map fun β ↦ nsq (β.vec x)).sum ≤ 1) :
    (E.map fun β ↦ nsq (meanV β.vec)).sum ≤
      2 / (2 ^ n : ℝ) + 2 / (2 ^ n : ℝ) * ∑ x, (1 - succ x E) := by
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  set N : ℝ := 2 ^ n with hNdef
  have hcard : ((Finset.univ : Finset (Fin (2 ^ n))).card : ℝ) = N := by
    rw [hNdef]; simp
  -- the branchwise quantities
  let g : Fin (2 ^ n) → Branch Var (Fin (2 ^ n)) Q → ℝ := fun x β ↦
    if (β.live && decide (β.store res = (x.val : ℤ))) = true then nsq (β.vec x) else 0
  let Tb : Branch Var (Fin (2 ^ n)) Q → Finset (Fin (2 ^ n)) := fun β ↦
    Finset.univ.filter fun x ↦ (β.live && decide (β.store res = (x.val : ℤ))) = true
  have hTb : ∀ β, (Tb β).card ≤ 1 := by
    intro β
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Tb, Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
      decide_eq_true_eq] at ha hb
    exact Fin.ext (by exact_mod_cast ha.2.symm.trans hb.2)
  have hTsum : ∀ β, ∑ x ∈ Tb β, nsq (β.vec x) = ∑ x, g x β := by
    intro β
    simp only [Tb, g]
    rw [Finset.sum_filter]
  have hbeta : ∀ β : Branch Var (Fin (2 ^ n)) Q, nsq (meanV β.vec) ≤
      2 / N ^ 2 * ∑ x, g x β + 2 / N * ((∑ x, nsq (β.vec x)) - ∑ x, g x β) := by
    intro β
    have h := nsq_meanV_split β.vec (Tb β) (hTb β)
    have hc := Finset.sum_compl_add_sum (Tb β) (fun x ↦ nsq (β.vec x))
    rw [hTsum β] at h hc
    have : ∑ x ∈ (Tb β)ᶜ, nsq (β.vec x) = (∑ x, nsq (β.vec x)) - ∑ x, g x β := by linarith
    rw [this] at h
    exact h
  have hsum1 : (E.map fun β ↦ nsq (meanV β.vec)).sum ≤
      (E.map fun β ↦ 2 / N ^ 2 * ∑ x, g x β +
        2 / N * ((∑ x, nsq (β.vec x)) - ∑ x, g x β)).sum :=
    List.sum_le_sum fun β _ => hbeta β
  rw [list_sum_lin] at hsum1
  have hA : (E.map fun β ↦ ∑ x, g x β).sum = ∑ x, succ x E := by
    rw [← finset_sum_list_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold succ
    rw [sum_filter_ite]
  have hM : (E.map fun β ↦ ∑ x, nsq (β.vec x)).sum =
      ∑ x, (E.map fun β ↦ nsq (β.vec x)).sum := (finset_sum_list_sum E _).symm
  have hsx : ∀ x, succ x E ≤ 1 := by
    intro x
    refine le_trans ?_ (hmass x)
    unfold succ
    rw [sum_filter_ite]
    refine List.sum_le_sum fun β _ => ?_
    split_ifs
    · exact le_rfl
    · exact nsq_nonneg _
  have hAle : ∑ x, succ x E ≤ N := by
    calc ∑ x, succ x E ≤ ∑ _x : Fin (2 ^ n), (1 : ℝ) := Finset.sum_le_sum fun x _ => hsx x
      _ = N := by simp [hNdef]
  have hMle : (E.map fun β ↦ ∑ x, nsq (β.vec x)).sum ≤ N := by
    rw [hM]
    calc _ ≤ ∑ _x : Fin (2 ^ n), (1 : ℝ) := Finset.sum_le_sum fun x _ => hmass x
      _ = N := by simp [hNdef]
  rw [hA, hM] at hsum1
  rw [hM] at hMle
  have hR : ∑ x, (1 - succ x E) = N - ∑ x, succ x E := by
    rw [Finset.sum_sub_distrib]
    simp [hNdef]
  rw [hR]
  set A := ∑ x, succ x E with hAdef
  set M := ∑ x, (E.map fun β ↦ nsq (β.vec x)).sum with hMdef
  have e1 : 2 / N ^ 2 * A ≤ 2 / N := by
    have h1 : 2 / N ^ 2 * A ≤ 2 / N ^ 2 * N := by gcongr
    have h2 : 2 / N ^ 2 * N = 2 / N := by field_simp
    linarith
  have e2 : 2 / N * (M - A) ≤ 2 / N * (N - A) := by
    have : 0 ≤ 2 / N := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) this
  linarith

end summed

end GroverThreeFifths

#print axioms GroverThreeFifths.rep_cost_all
#print axioms GroverThreeFifths.mass_ens_le
#print axioms GroverThreeFifths.nsq_meanV_split
#print axioms GroverThreeFifths.sum_meanV_le
