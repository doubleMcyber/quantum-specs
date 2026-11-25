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
import LowerBounds.Grover.FullPotential
import Mathlib

/-!
# One oracle call against the potential `Vf`

`Vf_query`: one oracle call lowers `κ * Vf` by at most the branch weight `W`, where
`κ = 2 / arcsin (2 / t)` and `t = √(2 ^ n)`. The proof goes through the angle
`φ = arccos √(C / W)`, on which `gf (cos φ ^ 2)` is `1/2`-Lipschitz.

`kappa_pos`, `sqrt_le_kappa` and `kappa_end` are the facts about `κ` that `FullBound.lean` uses.
-/

open QuantumComputation.Specs Operator ResourceCounting Filter
open scoped Matrix QHLExpectation ComplexOrder MatrixOrder ENNReal NNReal
open QuantumComputation.Specs.Grover (Var)
open QuantumComputation.Specs.Grover.Var (res)

namespace GroverThreeFifths

open GroverLowerBound

/-! ### `gf ∘ cos²` -/

lemma cos_sq_ge_half {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ Real.pi / 4) : 1 / 2 ≤ Real.cos φ ^ 2 := by
  have h := Real.cos_two_mul φ
  have hc : 0 ≤ Real.cos (2 * φ) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) (by linarith)
  linarith

lemma gf_cos_sq_small {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ Real.pi / 4) :
    gf (Real.cos φ ^ 2) = Real.pi / 8 + 1 / 4 - φ / 2 := by
  rw [gf_of_ge (cos_sq_ge_half h0 h1)]
  have e : 2 * Real.cos φ ^ 2 - 1 = Real.sin (Real.pi / 2 - 2 * φ) := by
    rw [Real.sin_pi_div_two_sub, Real.cos_two_mul]
  rw [e, Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith)]
  ring

lemma gf_cos_sq_large {φ : ℝ} (h0 : Real.pi / 4 ≤ φ) (h1 : φ ≤ Real.pi / 2) :
    gf (Real.cos φ ^ 2) = Real.cos φ ^ 2 / 2 := by
  apply gf_of_le
  have h := Real.cos_two_mul φ
  have hc : Real.cos (2 * φ) ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith [Real.pi_pos])
  linarith

lemma cos_sq_sub (a b : ℝ) :
    Real.cos a ^ 2 - Real.cos b ^ 2 = Real.sin (b + a) * Real.sin (b - a) := by
  rw [Real.sin_add, Real.sin_sub]
  have ha := Real.sin_sq_add_cos_sq a
  have hb := Real.sin_sq_add_cos_sq b
  linear_combination (-(Real.cos a ^ 2)) * hb + (Real.cos b ^ 2) * ha

lemma gf_cos_sq_lip_large {a b : ℝ} (ha : Real.pi / 4 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2) :
    gf (Real.cos a ^ 2) - gf (Real.cos b ^ 2) ≤ (b - a) / 2 := by
  rw [gf_cos_sq_large ha (hab.trans hb), gf_cos_sq_large (ha.trans hab) hb]
  have h1 : 0 ≤ Real.sin (b + a) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have h2 : 0 ≤ Real.sin (b - a) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have h3 : Real.sin (b + a) ≤ 1 := Real.sin_le_one _
  have h4 : Real.sin (b - a) ≤ b - a := Real.sin_le (by linarith)
  have h5 := cos_sq_sub a b
  have h6 := mul_le_mul h3 h4 h2 zero_le_one
  linarith

/-- `gf (cos φ ^ 2)` is `1/2`-Lipschitz and nonincreasing in the one-sided form used by the query. -/
lemma gf_cos_sq_lip {φ φ' : ℝ} (h0 : 0 ≤ φ) (h : φ ≤ φ') (h1 : φ' ≤ Real.pi / 2) :
    gf (Real.cos φ ^ 2) - gf (Real.cos φ' ^ 2) ≤ (φ' - φ) / 2 := by
  rcases le_total φ' (Real.pi / 4) with hb | hb
  · rw [gf_cos_sq_small h0 (h.trans hb), gf_cos_sq_small (h0.trans h) hb]
    linarith
  · rcases le_total φ (Real.pi / 4) with ha | ha
    · have s1 := gf_cos_sq_small h0 ha
      have s2 := gf_cos_sq_small (by linarith [Real.pi_pos] : 0 ≤ Real.pi / 4) le_rfl
      have l := gf_cos_sq_lip_large (le_refl (Real.pi / 4)) hb h1
      linarith
    · exact gf_cos_sq_lip_large ha h h1

/-! ### Facts about `β = arcsin (2 / t)` -/

lemma cos_arcsin_le (t : ℝ) (ht : 2 ≤ t) : Real.cos (Real.arcsin (2 / t)) ≤ 1 - 2 / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  rw [Real.cos_arcsin]
  have h1 : 0 ≤ 1 - 2 / t ^ 2 := by
    have : 2 / t ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    linarith
  apply Real.sqrt_le_iff.2 ⟨h1, ?_⟩
  have e : (2 / t) ^ 2 = 2 * (2 / t ^ 2) := by ring
  rw [e]
  nlinarith [sq_nonneg (2 / t ^ 2)]

theorem kappa_pos (t : ℝ) (ht : 2 ≤ t) : 0 < 2 / Real.arcsin (2 / t) := by
  have ht0 : 0 < t := by linarith
  exact div_pos two_pos (Real.arcsin_pos.2 (div_pos two_pos ht0))

/-! ### The query step -/

theorem Vf_query (t C W C' : ℝ) (ht : 2 ≤ t) (hC : 0 ≤ C) (hCW : C ≤ W) (hC' : 0 ≤ C')
    (hC'W : C' ≤ W)
    (h : (1 - 2 / t ^ 2) * Real.sqrt C - 2 / t * Real.sqrt (W - C) ≤ Real.sqrt C') :
    (2 / Real.arcsin (2 / t)) * Vf C W - W ≤ (2 / Real.arcsin (2 / t)) * Vf C' W := by
  have ht0 : 0 < t := by linarith
  have hW0 : 0 ≤ W := hC.trans hCW
  rcases hW0.eq_or_lt with hW | hW
  · subst hW
    have h1 : C = 0 := le_antisymm hCW hC
    have h2 : C' = 0 := le_antisymm hC'W hC'
    subst h1; subst h2
    simp [Vf_00]
  · have h2t : 0 < 2 / t := div_pos two_pos ht0
    obtain ⟨β, hβ⟩ : ∃ β, β = Real.arcsin (2 / t) := ⟨_, rfl⟩
    have hβpos : 0 < β := by rw [hβ]; exact Real.arcsin_pos.2 h2t
    have hβle : β ≤ Real.pi / 2 := by rw [hβ]; exact Real.arcsin_le_pi_div_two _
    have hsinβ : Real.sin β = 2 / t := by
      rw [hβ]; exact Real.sin_arcsin (by linarith) ((div_le_one ht0).2 ht)
    have hcosβ : Real.cos β ≤ 1 - 2 / t ^ 2 := by rw [hβ]; exact cos_arcsin_le t ht
    have hr0 : 0 ≤ C / W := div_nonneg hC hW.le
    have hr1 : C / W ≤ 1 := (div_le_one hW).2 hCW
    have hr0' : 0 ≤ C' / W := div_nonneg hC' hW.le
    have hr1' : C' / W ≤ 1 := (div_le_one hW).2 hC'W
    have hs1 : Real.sqrt (C / W) ≤ 1 := (Real.sqrt_le_sqrt hr1).trans_eq Real.sqrt_one
    have hs1' : Real.sqrt (C' / W) ≤ 1 := (Real.sqrt_le_sqrt hr1').trans_eq Real.sqrt_one
    have hsW : 0 ≤ Real.sqrt W := Real.sqrt_nonneg W
    obtain ⟨φ, hφ⟩ : ∃ φ, φ = Real.arccos (Real.sqrt (C / W)) := ⟨_, rfl⟩
    obtain ⟨φ', hφ'⟩ : ∃ φ', φ' = Real.arccos (Real.sqrt (C' / W)) := ⟨_, rfl⟩
    have hφ0 : 0 ≤ φ := by rw [hφ]; exact Real.arccos_nonneg _
    have hφ0' : 0 ≤ φ' := by rw [hφ']; exact Real.arccos_nonneg _
    have hφ1 : φ ≤ Real.pi / 2 := by
      rw [hφ]; exact Real.arccos_le_pi_div_two.2 (Real.sqrt_nonneg _)
    have hφ1' : φ' ≤ Real.pi / 2 := by
      rw [hφ']; exact Real.arccos_le_pi_div_two.2 (Real.sqrt_nonneg _)
    have hcφ0 : Real.cos φ = Real.sqrt (C / W) := by
      rw [hφ]; exact Real.cos_arccos (by linarith [Real.sqrt_nonneg (C / W)]) hs1
    have hcφ0' : Real.cos φ' = Real.sqrt (C' / W) := by
      rw [hφ']; exact Real.cos_arccos (by linarith [Real.sqrt_nonneg (C' / W)]) hs1'
    have hsq : Real.cos φ ^ 2 = C / W := by rw [hcφ0, Real.sq_sqrt hr0]
    have hsq' : Real.cos φ' ^ 2 = C' / W := by rw [hcφ0', Real.sq_sqrt hr0']
    have hcφ : Real.cos φ = Real.sqrt C * (Real.sqrt W)⁻¹ := by
      rw [hcφ0, Real.sqrt_div hC, div_eq_mul_inv]
    have hcφ' : Real.cos φ' = Real.sqrt C' * (Real.sqrt W)⁻¹ := by
      rw [hcφ0', Real.sqrt_div hC', div_eq_mul_inv]
    have hsφ : Real.sin φ = Real.sqrt (W - C) * (Real.sqrt W)⁻¹ := by
      rw [hφ, Real.sin_arccos, Real.sq_sqrt hr0]
      have e : 1 - C / W = (W - C) / W := by field_simp
      rw [e, Real.sqrt_div (by linarith), div_eq_mul_inv]
    have hcφnn : 0 ≤ Real.cos φ := by rw [hcφ0]; exact Real.sqrt_nonneg _
    have h' : (1 - 2 / t ^ 2) * Real.cos φ - 2 / t * Real.sin φ ≤ Real.cos φ' := by
      rw [hcφ, hsφ, hcφ']
      have := mul_le_mul_of_nonneg_right h (inv_nonneg.2 hsW)
      linarith
    have hcos : Real.cos (φ + β) ≤ Real.cos φ' := by
      rw [Real.cos_add, hsinβ]
      have h1 := mul_le_mul_of_nonneg_left hcosβ hcφnn
      linarith
    have hφφ' : φ' ≤ φ + β := by
      by_contra hlt
      push_neg at hlt
      have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := φ + β) (y := φ') (by linarith)
        (by linarith [Real.pi_pos]) hlt
      linarith
    have key : gf (C / W) - gf (C' / W) ≤ β / 2 := by
      rcases le_total φ φ' with hle | hle
      · have := gf_cos_sq_lip hφ0 hle hφ1'
        rw [hsq, hsq'] at this
        linarith
      · have hc : Real.cos φ ≤ Real.cos φ' :=
          Real.cos_le_cos_of_nonneg_of_le_pi hφ0' (by linarith [Real.pi_pos]) hle
        have hm : C / W ≤ C' / W := by
          rw [← hsq, ← hsq']
          exact pow_le_pow_left₀ hcφnn hc 2
        have := gf_monotoneOn ⟨hr0, hr1⟩ ⟨hr0', hr1'⟩ hm
        linarith
    rw [← hβ, Vf_of_pos hW, Vf_of_pos hW]
    have hk : 0 ≤ 2 / β := by positivity
    have e : (2 / β * W) * (β / 2) = W := by field_simp
    have := mul_le_mul_of_nonneg_left key (mul_nonneg hk hW.le)
    nlinarith [this, e]

/-! ### Numeric facts about `κ` -/

/-- κ is at least √(t² − 4). -/
theorem sqrt_le_kappa (t : ℝ) (ht : 2 ≤ t) : Real.sqrt (t ^ 2 - 4) ≤ 2 / Real.arcsin (2 / t) := by
  have ht0 : 0 < t := by linarith
  have h2t : 0 < 2 / t := div_pos two_pos ht0
  have hβpos : 0 < Real.arcsin (2 / t) := Real.arcsin_pos.2 h2t
  rw [le_div_iff₀ hβpos]
  rcases ht.eq_or_lt with h | h
  · subst h
    norm_num
  · have h1 : 2 / t < 1 := (div_lt_one ht0).2 h
    have hx : Real.arcsin (2 / t) < Real.pi / 2 := Real.arcsin_lt_pi_div_two.2 h1
    have hcpos : 0 < Real.cos (Real.arcsin (2 / t)) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hx⟩
    have hle := Real.le_tan hβpos.le hx
    rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hcpos,
      Real.sin_arcsin (by linarith) h1.le, Real.cos_arcsin] at hle
    have h2 : t * (2 / t) = 2 := by field_simp
    have h3 : t ^ 2 - 4 = t ^ 2 * (1 - (2 / t) ^ 2) := by
      have : t ^ 2 * (2 / t) ^ 2 = 4 := by rw [← mul_pow, h2]; norm_num
      linear_combination this
    have e : Real.sqrt (t ^ 2 - 4) = t * Real.sqrt (1 - (2 / t) ^ 2) := by
      rw [h3, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht0.le]
    rw [e]
    calc t * Real.sqrt (1 - (2 / t) ^ 2) * Real.arcsin (2 / t)
        = t * (Real.arcsin (2 / t) * Real.sqrt (1 - (2 / t) ^ 2)) := by ring
      _ ≤ t * (2 / t) := mul_le_mul_of_nonneg_left hle ht0.le
      _ = 2 := h2

/-- The end bound used by the assembly. -/
theorem kappa_end (t : ℝ) (ht : 2 ≤ t) :
    (Real.pi / 8 + 1 / 4) * t - 4 / t ≤
      (2 / Real.arcsin (2 / t)) * ((Real.pi / 8 + 1 / 4) * (1 - 2 / t ^ 2)) := by
  have ht0 : 0 < t := by linarith
  have hK := sqrt_le_kappa t ht
  have hs : t - 4 / t ≤ Real.sqrt (t ^ 2 - 4) := by
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    have h1 : 16 / t ^ 2 ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have e : (t - 4 / t) ^ 2 = t ^ 2 - 8 + 16 / t ^ 2 := by
      field_simp <;> ring
    rw [e]; linarith
  have hc0 : 0 ≤ Real.pi / 8 + 1 / 4 := by positivity
  have h1' : 0 ≤ 1 - 2 / t ^ 2 := by
    have : 2 / t ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    linarith
  have hq : 0 ≤ (Real.pi / 8 + 1 / 4) * (1 - 2 / t ^ 2) := mul_nonneg hc0 h1'
  have h2 := mul_le_mul_of_nonneg_right (hs.trans hK) hq
  have e : (t - 4 / t) * ((Real.pi / 8 + 1 / 4) * (1 - 2 / t ^ 2))
      = (Real.pi / 8 + 1 / 4) * t - 6 * (Real.pi / 8 + 1 / 4) / t
        + 8 * (Real.pi / 8 + 1 / 4) / t ^ 3 := by
    field_simp <;> ring
  have h3 : 0 ≤ (4 - 6 * (Real.pi / 8 + 1 / 4)) / t :=
    div_nonneg (by linarith [Real.pi_lt_d2]) ht0.le
  have h4 : 0 ≤ 8 * (Real.pi / 8 + 1 / 4) / t ^ 3 := by positivity
  have e2 : (4 - 6 * (Real.pi / 8 + 1 / 4)) / t = 4 / t - 6 * (Real.pi / 8 + 1 / 4) / t := by
    ring
  linarith

end GroverThreeFifths

#print axioms GroverThreeFifths.Vf_query
#print axioms GroverThreeFifths.kappa_pos
#print axioms GroverThreeFifths.sqrt_le_kappa
#print axioms GroverThreeFifths.kappa_end
