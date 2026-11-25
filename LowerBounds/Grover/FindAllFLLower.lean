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
import LowerBounds.Grover.FindAllJohnsonPotential
import LowerBounds.Grover.FindAllOneSlotStatement
import Mathlib

/-!
# A lower bound for `FL`

`FL_lower`: for `1 ≤ k` and `4 k ≤ N`,
`(1 / 2 - 2 k / N) * groverHarmonicSqrtSum k * √N ≤ FL N (k - 1)`.
-/

namespace GroverParallel
open QuantumComputation.Specs Real

private lemma jdelta_lower (N k' i : ℕ) (hN : 4 * (k' + 1) ≤ N) (hi : i ≤ k') :
    √((N : ℝ) - 2 * ((k' : ℝ) + 1)) / (2 * √((k' : ℝ) + 1 - i)) ≤ jdelta N k' i := by
  have hiR : (i : ℝ) ≤ k' := by exact_mod_cast hi
  have hNR : 4 * ((k' : ℝ) + 1) ≤ N := by exact_mod_cast hN
  have hk0 : (0 : ℝ) ≤ k' := Nat.cast_nonneg k'
  have hu : 0 < (k' : ℝ) + 1 - i := by linarith
  have hv : 0 < (N : ℝ) - k' - 1 - i := by linarith
  have hM : 0 ≤ (N : ℝ) - 2 * ((k' : ℝ) + 1) := by linarith
  have hMv : (N : ℝ) - 2 * ((k' : ℝ) + 1) ≤ (N : ℝ) - k' - 1 - i := by linarith
  have key : √((N : ℝ) - 2 * ((k' : ℝ) + 1)) * √((N : ℝ) - k' - 1 - i) ≤ (N : ℝ) - 2 * i := by
    have h1 : √((N : ℝ) - 2 * ((k' : ℝ) + 1)) ≤ √((N : ℝ) - k' - 1 - i) :=
      Real.sqrt_le_sqrt hMv
    have h2 : √((N : ℝ) - k' - 1 - i) * √((N : ℝ) - k' - 1 - i) = (N : ℝ) - k' - 1 - i :=
      Real.mul_self_sqrt hv.le
    have h3 : √((N : ℝ) - 2 * ((k' : ℝ) + 1)) * √((N : ℝ) - k' - 1 - i) ≤
        √((N : ℝ) - k' - 1 - i) * √((N : ℝ) - k' - 1 - i) :=
      mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
    linarith
  unfold jdelta jc
  rw [Real.sqrt_mul hu.le]
  have hsu : 0 < √((k' : ℝ) + 1 - i) := Real.sqrt_pos.2 hu
  have hsv : 0 < √((N : ℝ) - k' - 1 - i) := Real.sqrt_pos.2 hv
  rw [div_le_div_iff₀ (mul_pos two_pos hsu) (mul_pos two_pos (mul_pos hsu hsv))]
  have h := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 2 * √((k' : ℝ) + 1 - i))
  nlinarith [h]

private lemma jdelta_nonneg (N k' i : ℕ) (hN : 4 * (k' + 1) ≤ N) (hi : i ≤ k') :
    0 ≤ jdelta N k' i := by
  have hiR : (i : ℝ) ≤ k' := by exact_mod_cast hi
  have hNR : 4 * ((k' : ℝ) + 1) ≤ N := by exact_mod_cast hN
  have hk0 : (0 : ℝ) ≤ k' := Nat.cast_nonneg k'
  unfold jdelta
  apply div_nonneg
  · linarith
  · positivity

private lemma choose_ratio (N k' i : ℕ) (hN : 4 * (k' + 1) ≤ N) (hi : i ≤ k') :
    (N.choose i : ℝ) / (N.choose (k' + 1) : ℝ) ≤
      ((k' : ℝ) + 1) / ((N : ℝ) - ((k' : ℝ) + 1) + 1) := by
  have hmono : ∀ d, i + d ≤ k' → N.choose i ≤ N.choose (i + d) := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro h
      exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
  have h1 : N.choose i ≤ N.choose k' := by
    have := hmono (k' - i) (by omega)
    rwa [show i + (k' - i) = k' by omega] at this
  have h2 := Nat.choose_succ_right_eq N k'
  have hk'N : k' ≤ N := by omega
  have hP : (0 : ℝ) < N.choose (k' + 1) := by exact_mod_cast Nat.choose_pos (by omega)
  have hNR : 4 * ((k' : ℝ) + 1) ≤ N := by exact_mod_cast hN
  have hk0 : (0 : ℝ) ≤ k' := Nat.cast_nonneg k'
  have e : (N : ℝ) - ((k' : ℝ) + 1) + 1 = (N : ℝ) - k' := by ring
  have hd : (0 : ℝ) < (N : ℝ) - k' := by linarith
  have h2R : (N.choose (k' + 1) : ℝ) * ((k' : ℝ) + 1) = (N.choose k' : ℝ) * ((N : ℝ) - k') := by
    have := congrArg (Nat.cast (R := ℝ)) h2
    push_cast [Nat.cast_sub hk'N] at this
    exact this
  have h1R : (N.choose i : ℝ) ≤ N.choose k' := by exact_mod_cast h1
  rw [e, div_le_div_iff₀ hP hd]
  have h3 : (N.choose i : ℝ) * ((N : ℝ) - k') ≤ N.choose k' * ((N : ℝ) - k') :=
    mul_le_mul_of_nonneg_right h1R hd.le
  linarith

private lemma one_sub_nonneg' (n x : ℝ) (hx : 1 ≤ x) (hn : 4 * x ≤ n) :
    0 ≤ 1 - x / (n - x + 1) := by
  have hd : 0 < n - x + 1 := by linarith
  rw [sub_nonneg, div_le_one hd]
  linarith

private lemma arith_final (n x : ℝ) (hx : 1 ≤ x) (hn : 4 * x ≤ n) :
    (1 / 2 - 2 * x / n) * √n ≤ √(n - 2 * x) / 2 * (1 - x / (n - x + 1)) := by
  have hn0 : 0 < n := by linarith
  have hd : 0 < n - x + 1 := by linarith
  have hs0 : 0 < √n := Real.sqrt_pos.2 hn0
  have hM : 0 ≤ n - 2 * x := by linarith
  have ht0 : 0 ≤ √(n - 2 * x) := Real.sqrt_nonneg _
  have hts : √(n - 2 * x) ≤ √n := Real.sqrt_le_sqrt (by linarith)
  have hs2 : √n * √n = n := Real.mul_self_sqrt hn0.le
  have ht2 : √(n - 2 * x) * √(n - 2 * x) = n - 2 * x := Real.mul_self_sqrt hM
  have hT : (n - 2 * x) / n * √n ≤ √(n - 2 * x) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hn0]
    have e : √(n - 2 * x) * n - (n - 2 * x) * √n =
        √(n - 2 * x) * √n * (√n - √(n - 2 * x)) := by
      linear_combination (-√(n - 2 * x)) * hs2 + √n * ht2
    have : 0 ≤ √(n - 2 * x) * √n * (√n - √(n - 2 * x)) :=
      mul_nonneg (mul_nonneg ht0 hs0.le) (sub_nonneg.2 hts)
    linarith
  have hq := one_sub_nonneg' n x hx hn
  have hcoef : (1 / 2 - 2 * x / n) ≤ (1 / 2) * ((n - 2 * x) / n) * (1 - x / (n - x + 1)) := by
    rw [← sub_nonneg]
    have hn' := hn0.ne'
    have hd' := hd.ne'
    have e : (1 / 2) * ((n - 2 * x) / n) * (1 - x / (n - x + 1)) - (1 / 2 - 2 * x / n) =
        (n * x + 2 * x) / (2 * n * (n - x + 1)) := by
      field_simp
      ring
    rw [e]
    apply div_nonneg
    · have := mul_pos hn0 (by linarith : 0 < x)
      linarith
    · exact (mul_pos (mul_pos two_pos hn0) hd).le
  calc (1 / 2 - 2 * x / n) * √n
      ≤ ((1 / 2) * ((n - 2 * x) / n) * (1 - x / (n - x + 1))) * √n :=
        mul_le_mul_of_nonneg_right hcoef hs0.le
    _ = (1 / 2) * ((n - 2 * x) / n * √n) * (1 - x / (n - x + 1)) := by ring
    _ ≤ (1 / 2) * √(n - 2 * x) * (1 - x / (n - x + 1)) := by
        refine mul_le_mul_of_nonneg_right ?_ hq
        exact mul_le_mul_of_nonneg_left hT (by norm_num)
    _ = √(n - 2 * x) / 2 * (1 - x / (n - x + 1)) := by ring

private lemma icc_eq_range (g : ℕ → ℝ) (n : ℕ) :
    ∑ r ∈ Finset.Icc 1 n, g r = ∑ j ∈ Finset.range n, g (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

private lemma harmonic_reflect (k' : ℕ) :
    groverHarmonicSqrtSum (k' + 1) =
      ∑ i ∈ Finset.range (k' + 1), 1 / √((k' : ℝ) + 1 - i) := by
  unfold groverHarmonicSqrtSum
  rw [icc_eq_range (fun r => 1 / √(r : ℝ)) (k' + 1)]
  calc ∑ j ∈ Finset.range (k' + 1), (fun r : ℕ => 1 / √(r : ℝ)) (j + 1)
      = ∑ j ∈ Finset.range (k' + 1), (fun j : ℕ => 1 / √(((j : ℕ) : ℝ) + 1)) j := by
        apply Finset.sum_congr rfl
        intro j _
        simp
    _ = ∑ j ∈ Finset.range (k' + 1),
          (fun j : ℕ => 1 / √(((j : ℕ) : ℝ) + 1)) (k' + 1 - 1 - j) :=
        (Finset.sum_range_reflect (fun j : ℕ => 1 / √(((j : ℕ) : ℝ) + 1)) (k' + 1)).symm
    _ = ∑ i ∈ Finset.range (k' + 1), 1 / √((k' : ℝ) + 1 - i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i ≤ k' := by have := Finset.mem_range.1 hi; omega
        dsimp only
        have e : k' + 1 - 1 - i = k' - i := by omega
        rw [e, Nat.cast_sub hi']
        congr 2
        ring

theorem FL_lower (N k : ℕ) (hk : 1 ≤ k) (hN : 4 * k ≤ N) :
    (1 / 2 - 2 * (k : ℝ) / N) * groverHarmonicSqrtSum k * √(N : ℝ) ≤ FL N (k - 1) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hc : (((k' + 1 : ℕ)) : ℝ) = (k' : ℝ) + 1 := by push_cast; ring
  rw [hc, Nat.add_sub_cancel, harmonic_reflect k']
  have hNR : 4 * ((k' : ℝ) + 1) ≤ N := by exact_mod_cast hN
  have hk0 : (0 : ℝ) ≤ k' := Nat.cast_nonneg k'
  have hx : (1 : ℝ) ≤ (k' : ℝ) + 1 := by linarith
  have hF := arith_final (N : ℝ) ((k' : ℝ) + 1) hx hNR
  have hq := one_sub_nonneg' (N : ℝ) ((k' : ℝ) + 1) hx hNR
  have hterm : ∀ i ∈ Finset.range (k' + 1),
      ((1 / 2 - 2 * ((k' : ℝ) + 1) / N) * √(N : ℝ)) * (1 / √((k' : ℝ) + 1 - i)) ≤
        jdelta N k' i * (1 - (N.choose i : ℝ) / (N.choose (k' + 1) : ℝ)) := by
    intro i hi
    have hi' : i ≤ k' := by have := Finset.mem_range.1 hi; omega
    have hiR : (i : ℝ) ≤ k' := by exact_mod_cast hi'
    have hu : 0 < (k' : ℝ) + 1 - i := by linarith
    have hsu : 0 < √((k' : ℝ) + 1 - i) := Real.sqrt_pos.2 hu
    have hA := jdelta_lower N k' i hN hi'
    have hB : 1 - ((k' : ℝ) + 1) / ((N : ℝ) - ((k' : ℝ) + 1) + 1) ≤
        1 - (N.choose i : ℝ) / (N.choose (k' + 1) : ℝ) := by
      linarith [choose_ratio N k' i hN hi']
    have hpos : (0 : ℝ) ≤ 1 / √((k' : ℝ) + 1 - i) := by positivity
    calc ((1 / 2 - 2 * ((k' : ℝ) + 1) / N) * √(N : ℝ)) * (1 / √((k' : ℝ) + 1 - i))
        ≤ (√((N : ℝ) - 2 * ((k' : ℝ) + 1)) / 2 *
            (1 - ((k' : ℝ) + 1) / ((N : ℝ) - ((k' : ℝ) + 1) + 1))) *
            (1 / √((k' : ℝ) + 1 - i)) := mul_le_mul_of_nonneg_right hF hpos
      _ = (√((N : ℝ) - 2 * ((k' : ℝ) + 1)) / (2 * √((k' : ℝ) + 1 - i))) *
            (1 - ((k' : ℝ) + 1) / ((N : ℝ) - ((k' : ℝ) + 1) + 1)) := by
          have := hsu.ne'
          field_simp
      _ ≤ jdelta N k' i * (1 - (N.choose i : ℝ) / (N.choose (k' + 1) : ℝ)) :=
          mul_le_mul hA hB hq (jdelta_nonneg N k' i hN hi')
  unfold FL
  calc (1 / 2 - 2 * ((k' : ℝ) + 1) / N) *
        (∑ i ∈ Finset.range (k' + 1), 1 / √((k' : ℝ) + 1 - i)) * √(N : ℝ)
      = ∑ i ∈ Finset.range (k' + 1),
          ((1 / 2 - 2 * ((k' : ℝ) + 1) / N) * √(N : ℝ)) * (1 / √((k' : ℝ) + 1 - i)) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ _ := Finset.sum_le_sum hterm

end GroverParallel

#print axioms GroverParallel.FL_lower
