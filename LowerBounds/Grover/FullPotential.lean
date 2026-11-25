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
import LowerBounds.Grover.ThreeFifthsBound
import Mathlib

/-!
# The potential for the constant π/8 + 1/4

`Vf (C, W) = W * gf (C / W)`, where `gf r = r / 2` for `r ≤ 1 / 2` and
`gf r = 1 / 4 + arcsin (2 r - 1) / 4` for `r > 1 / 2`.

`gf` is convex and nondecreasing on `[0, 1]` with `gf 1 = π / 8 + 1 / 4`, so `Vf` is subadditive on
pairs `0 ≤ C ≤ W`. That gives `Vf_measure`: after a computational-basis measurement of any register,
the sum of `Vf` over the outcome branches, computed from the unnormalised branch vectors, is at least
`Vf` before the measurement.
-/

open QuantumComputation.Specs Operator ResourceCounting Filter
open scoped Matrix QHLExpectation ComplexOrder MatrixOrder ENNReal NNReal
open QuantumComputation.Specs.Grover (Var)
open QuantumComputation.Specs.Grover.Var (res)

namespace GroverThreeFifths

open GroverLowerBound

noncomputable def gf (r : ℝ) : ℝ := if r ≤ 1 / 2 then r / 2 else 1 / 4 + Real.arcsin (2 * r - 1) / 4
noncomputable def Vf (C W : ℝ) : ℝ := if W ≤ 0 then 0 else W * gf (C / W)

/-! ### Values of `gf` -/

lemma gf_of_le {r : ℝ} (h : r ≤ 1 / 2) : gf r = r / 2 := by
  unfold gf; rw [if_pos h]

lemma gf_of_gt {r : ℝ} (h : 1 / 2 < r) : gf r = 1 / 4 + Real.arcsin (2 * r - 1) / 4 := by
  unfold gf; rw [if_neg (not_le.2 h)]

lemma gf_of_ge {r : ℝ} (h : 1 / 2 ≤ r) : gf r = 1 / 4 + Real.arcsin (2 * r - 1) / 4 := by
  rcases h.eq_or_lt with h | h
  · subst h
    rw [gf_of_le le_rfl]
    norm_num [Real.arcsin_zero]
  · exact gf_of_gt h

lemma gf_zero : gf 0 = 0 := by
  rw [gf_of_le (by norm_num)]; norm_num

theorem gf_one : gf 1 = Real.pi / 8 + 1 / 4 := by
  have h : (2 : ℝ) * 1 - 1 = 1 := by norm_num
  rw [gf_of_gt (by norm_num), h, Real.arcsin_one]
  ring

/-! ### Supporting lines -/

lemma sin_tangent {a a0 : ℝ} (ha : a ∈ Set.Icc 0 Real.pi) (ha0 : a0 ∈ Set.Icc 0 Real.pi) :
    Real.sin a ≤ Real.sin a0 + Real.cos a0 * (a - a0) := by
  have hc : ConvexOn ℝ (Set.Icc 0 Real.pi) (fun x => -Real.sin x) :=
    strictConcaveOn_sin_Icc.concaveOn.neg
  have hd : HasDerivAt (fun x => -Real.sin x) (-Real.cos a0) a0 := (Real.hasDerivAt_sin a0).neg
  rcases lt_trichotomy a a0 with h | h | h
  · have h1 := hc.slope_le_of_hasDerivAt ha ha0 h hd
    rw [slope_def_field] at h1
    beta_reduce at h1
    rw [div_le_iff₀ (by linarith)] at h1
    nlinarith
  · subst h; simp
  · have h1 := hc.le_slope_of_hasDerivAt ha0 ha h hd
    rw [slope_def_field] at h1
    beta_reduce at h1
    rw [le_div_iff₀ (by linarith)] at h1
    nlinarith

lemma arcsin_tangent {y0 y : ℝ} (h0 : 0 ≤ y0) (h0' : y0 < 1) (hy : 0 ≤ y) (hy' : y ≤ 1) :
    y - y0 ≤ Real.sqrt (1 - y0 ^ 2) * (Real.arcsin y - Real.arcsin y0) := by
  have h := sin_tangent (a := Real.arcsin y) (a0 := Real.arcsin y0)
    ⟨Real.arcsin_nonneg.2 hy, by linarith [Real.arcsin_le_pi_div_two y, Real.pi_pos]⟩
    ⟨Real.arcsin_nonneg.2 h0, by linarith [Real.arcsin_le_pi_div_two y0, Real.pi_pos]⟩
  rw [Real.sin_arcsin (by linarith) hy', Real.sin_arcsin (by linarith) h0'.le,
    Real.cos_arcsin] at h
  linarith

/-- the slope of the supporting line at `r0` -/
noncomputable def sg (r0 : ℝ) : ℝ :=
  if r0 ≤ 1 / 2 then 1 / 2 else 1 / (4 * Real.sqrt (r0 * (1 - r0)))

lemma sg_ge (r0 : ℝ) (h1 : r0 < 1) : 1 / 2 ≤ sg r0 := by
  unfold sg
  split_ifs with h
  · exact le_rfl
  · push_neg at h
    have hs : 0 < Real.sqrt (r0 * (1 - r0)) :=
      Real.sqrt_pos.2 (mul_pos (by linarith) (by linarith))
    have hs2 : Real.sqrt (r0 * (1 - r0)) ≤ 1 / 2 := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, ?_⟩
      nlinarith [sq_nonneg (r0 - 1 / 2)]
    rw [le_div_iff₀ (by positivity)]
    linarith

lemma tangent_gf {r0 r : ℝ} (h : 1 / 2 < r0) (h1 : r0 < 1) (hr : 1 / 2 ≤ r) (hr1 : r ≤ 1) :
    gf r0 + sg r0 * (r - r0) ≤ gf r := by
  have hs : 0 < Real.sqrt (r0 * (1 - r0)) :=
    Real.sqrt_pos.2 (mul_pos (by linarith) (by linarith))
  have hsg : sg r0 = 1 / (4 * Real.sqrt (r0 * (1 - r0))) := by
    unfold sg; rw [if_neg (not_le.2 h)]
  have hT := arcsin_tangent (y0 := 2 * r0 - 1) (y := 2 * r - 1)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hq : Real.sqrt (1 - (2 * r0 - 1) ^ 2) = 2 * Real.sqrt (r0 * (1 - r0)) := by
    have e : 1 - (2 * r0 - 1) ^ 2 = 2 ^ 2 * (r0 * (1 - r0)) := by ring
    rw [e, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [hq] at hT
  rw [gf_of_gt h, gf_of_ge hr, hsg]
  have e2 : 1 / (4 * Real.sqrt (r0 * (1 - r0))) * (r - r0)
      = (r - r0) / (4 * Real.sqrt (r0 * (1 - r0))) := by ring
  rw [e2]
  have h2 : (r - r0) / (4 * Real.sqrt (r0 * (1 - r0)))
      ≤ (Real.arcsin (2 * r - 1) - Real.arcsin (2 * r0 - 1)) / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hT]
  linarith

lemma gf_ge_half {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : r / 2 ≤ gf r := by
  by_cases h : r ≤ 1 / 2
  · rw [gf_of_le h]
  · push_neg at h
    have hy : 0 ≤ 2 * r - 1 := by linarith
    have hA := Real.sin_le (Real.arcsin_nonneg.2 hy)
    rw [Real.sin_arcsin (by linarith) (by linarith)] at hA
    rw [gf_of_gt h]
    linarith

lemma gf_support {r0 r : ℝ} (h0 : 0 ≤ r0) (h1 : r0 < 1) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    gf r0 + sg r0 * (r - r0) ≤ gf r := by
  by_cases hr0 : r0 ≤ 1 / 2
  · have hs : sg r0 = 1 / 2 := by unfold sg; rw [if_pos hr0]
    rw [hs, gf_of_le hr0]
    have := gf_ge_half hr hr1
    linarith
  · push_neg at hr0
    by_cases hh : 1 / 2 ≤ r
    · exact tangent_gf hr0 h1 hh hr1
    · push_neg at hh
      have hT := tangent_gf (r := 1 / 2) hr0 h1 le_rfl (by norm_num)
      rw [gf_of_le (le_refl _)] at hT
      have hsg := sg_ge r0 h1
      rw [gf_of_le hh.le]
      nlinarith [mul_nonneg (sub_nonneg.2 hsg) (sub_nonneg.2 hh.le)]

/-! ### Convexity, monotonicity -/

theorem gf_convexOn : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) gf := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  simp only [smul_eq_mul]
  obtain rfl : b = 1 - a := by linarith
  by_cases hz : a * x + (1 - a) * y < 1
  · have hz0 : 0 ≤ a * x + (1 - a) * y := by nlinarith
    have h1 := gf_support hz0 hz hx0 hx1
    have h2 := gf_support hz0 hz hy0 hy1
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
  · push_neg at hz
    rcases ha.eq_or_lt with h | h
    · subst h
      have : y = 1 := by nlinarith
      subst this
      simp
    · rcases hb.eq_or_lt with h' | h'
      · have ha1 : a = 1 := by linarith
        subst ha1
        have : x = 1 := by nlinarith
        subst this
        simp
      · have hx' : x = 1 := by nlinarith
        have hy' : y = 1 := by nlinarith
        subst hx'; subst hy'
        apply le_of_eq
        have e : a * 1 + (1 - a) * 1 = 1 := by ring
        rw [e]; ring

theorem gf_monotoneOn : MonotoneOn gf (Set.Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  by_cases hy2 : y ≤ 1 / 2
  · rw [gf_of_le hy2, gf_of_le (hxy.trans hy2)]; linarith
  · push_neg at hy2
    have hA : 0 ≤ Real.arcsin (2 * y - 1) := Real.arcsin_nonneg.2 (by linarith)
    rw [gf_of_gt hy2]
    by_cases hx2 : x ≤ 1 / 2
    · rw [gf_of_le hx2]; linarith
    · push_neg at hx2
      rw [gf_of_gt hx2]
      have := Real.arcsin_le_arcsin (show 2 * x - 1 ≤ 2 * y - 1 by linarith)
      linarith

lemma gf_nonneg {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : 0 ≤ gf r := by
  have := gf_monotoneOn ⟨le_rfl, zero_le_one⟩ ⟨h0, h1⟩ h0
  rwa [gf_zero] at this

theorem gf_le_mul (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : gf r ≤ (Real.pi / 8 + 1 / 4) * r := by
  have := gf_convexOn.2 (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
    (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
    (sub_nonneg.2 h1) h0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, gf_zero, gf_one] at this
  linarith

/-! ### The perspective `Vf` -/

lemma Vf_of_pos {C W : ℝ} (h : 0 < W) : Vf C W = W * gf (C / W) := by
  unfold Vf; rw [if_neg (not_le.2 h)]

lemma Vf_of_nonpos {C W : ℝ} (h : W ≤ 0) : Vf C W = 0 := by
  unfold Vf; rw [if_pos h]

lemma Vf_00 : Vf 0 0 = 0 := Vf_of_nonpos le_rfl

theorem Vf_add (C₁ W₁ C₂ W₂ : ℝ) (h₁ : 0 ≤ C₁) (h₁' : C₁ ≤ W₁) (h₂ : 0 ≤ C₂) (h₂' : C₂ ≤ W₂) :
    Vf (C₁ + C₂) (W₁ + W₂) ≤ Vf C₁ W₁ + Vf C₂ W₂ := by
  have hW1 : 0 ≤ W₁ := h₁.trans h₁'
  have hW2 : 0 ≤ W₂ := h₂.trans h₂'
  rcases hW1.eq_or_lt with e1 | p1
  · subst e1
    have : C₁ = 0 := le_antisymm h₁' h₁
    subst this
    simp [Vf_00]
  · rcases hW2.eq_or_lt with e2 | p2
    · subst e2
      have : C₂ = 0 := le_antisymm h₂' h₂
      subst this
      simp [Vf_00]
    · have hs : 0 < W₁ + W₂ := add_pos p1 p2
      rw [Vf_of_pos hs, Vf_of_pos p1, Vf_of_pos p2]
      have hx : C₁ / W₁ ∈ Set.Icc (0 : ℝ) 1 := ⟨div_nonneg h₁ p1.le, (div_le_one p1).2 h₁'⟩
      have hy : C₂ / W₂ ∈ Set.Icc (0 : ℝ) 1 := ⟨div_nonneg h₂ p2.le, (div_le_one p2).2 h₂'⟩
      have hab : W₁ / (W₁ + W₂) + W₂ / (W₁ + W₂) = 1 := by
        rw [← add_div]; exact div_self hs.ne'
      have key := gf_convexOn.2 hx hy (div_nonneg p1.le hs.le) (div_nonneg p2.le hs.le) hab
      simp only [smul_eq_mul] at key
      have e : W₁ / (W₁ + W₂) * (C₁ / W₁) + W₂ / (W₁ + W₂) * (C₂ / W₂)
          = (C₁ + C₂) / (W₁ + W₂) := by
        field_simp
      rw [e] at key
      have ha : (W₁ + W₂) * (W₁ / (W₁ + W₂)) = W₁ := mul_div_cancel₀ _ hs.ne'
      have hb : (W₁ + W₂) * (W₂ / (W₁ + W₂)) = W₂ := mul_div_cancel₀ _ hs.ne'
      have := mul_le_mul_of_nonneg_left key hs.le
      calc (W₁ + W₂) * gf ((C₁ + C₂) / (W₁ + W₂))
          ≤ (W₁ + W₂) * (W₁ / (W₁ + W₂) * gf (C₁ / W₁) + W₂ / (W₁ + W₂) * gf (C₂ / W₂)) := this
        _ = ((W₁ + W₂) * (W₁ / (W₁ + W₂))) * gf (C₁ / W₁)
            + ((W₁ + W₂) * (W₂ / (W₁ + W₂))) * gf (C₂ / W₂) := by ring
        _ = W₁ * gf (C₁ / W₁) + W₂ * gf (C₂ / W₂) := by rw [ha, hb]

theorem Vf_fin_sum {k : ℕ} (C W : Fin k → ℝ) (h0 : ∀ o, 0 ≤ C o) (h1 : ∀ o, C o ≤ W o) :
    Vf (∑ o, C o) (∑ o, W o) ≤ ∑ o, Vf (C o) (W o) := by
  induction k with
  | zero => simp [Vf_00]
  | succ k ih =>
    simp only [Fin.sum_univ_succ]
    have hih := ih (fun i => C i.succ) (fun i => W i.succ) (fun i => h0 _) (fun i => h1 _)
    have hs0 : 0 ≤ ∑ i : Fin k, C i.succ := Finset.sum_nonneg fun i _ => h0 _
    have hs1 : ∑ i : Fin k, C i.succ ≤ ∑ i : Fin k, W i.succ :=
      Finset.sum_le_sum fun i _ => h1 _
    have := Vf_add (C 0) (W 0) _ _ (h0 0) (h1 0) hs0 hs1
    linarith

theorem Vf_self (W : ℝ) (hW : 0 ≤ W) : Vf W W = (Real.pi / 8 + 1 / 4) * W := by
  rcases hW.eq_or_lt with h | h
  · subst h; simp [Vf_00]
  · rw [Vf_of_pos h, div_self h.ne', gf_one]; ring

theorem Vf_le (C W : ℝ) (hC : 0 ≤ C) (hCW : C ≤ W) : Vf C W ≤ (Real.pi / 8 + 1 / 4) * C := by
  rcases (hC.trans hCW).eq_or_lt with h | h
  · have hC0 : C = 0 := by linarith
    rw [Vf_of_nonpos (by linarith), hC0]; simp
  · rw [Vf_of_pos h]
    have h1 := gf_le_mul (C / W) (div_nonneg hC h.le) ((div_le_one h).2 hCW)
    calc W * gf (C / W) ≤ W * ((Real.pi / 8 + 1 / 4) * (C / W)) :=
          mul_le_mul_of_nonneg_left h1 h.le
      _ = (Real.pi / 8 + 1 / 4) * C := by field_simp

theorem Vf_nonneg (C W : ℝ) (hC : 0 ≤ C) (hCW : C ≤ W) : 0 ≤ Vf C W := by
  by_cases h : W ≤ 0
  · rw [Vf_of_nonpos h]
  · push_neg at h
    rw [Vf_of_pos h]
    exact mul_nonneg h.le (gf_nonneg (div_nonneg hC h.le) ((div_le_one h).2 hCW))

/-- The unnormalized live-branch lemma after a computational-basis measurement of any register. -/
theorem Vf_measure {n Q k : ℕ} (r : QRegister k Q) (v : Fin (2 ^ n) → Fin (2 ^ Q) → ℂ) :
    Vf (nsq (meanV v)) (avgW v) ≤
      ∑ o : Fin (2 ^ k), Vf (nsq (meanV (fun i => (r.computationalBasisMeasurement.1 o) *ᵥ v i)))
        (avgW (fun i => (r.computationalBasisMeasurement.1 o) *ᵥ v i)) := by
  have h := Vf_fin_sum
    (fun o : Fin (2 ^ k) =>
      nsq (meanV (fun i => (r.computationalBasisMeasurement.1 o) *ᵥ v i)))
    (fun o => avgW (fun i => (r.computationalBasisMeasurement.1 o) *ᵥ v i))
    (fun o => nsq_nonneg _) (fun o => nsq_meanV_le _)
  rw [sum_nsq_meanV_measure, avgW_measure] at h
  exact h

end GroverThreeFifths

#print axioms GroverThreeFifths.gf_one
#print axioms GroverThreeFifths.gf_convexOn
#print axioms GroverThreeFifths.gf_monotoneOn
#print axioms GroverThreeFifths.gf_le_mul
#print axioms GroverThreeFifths.Vf_add
#print axioms GroverThreeFifths.Vf_fin_sum
#print axioms GroverThreeFifths.Vf_self
#print axioms GroverThreeFifths.Vf_le
#print axioms GroverThreeFifths.Vf_nonneg
#print axioms GroverThreeFifths.Vf_measure
