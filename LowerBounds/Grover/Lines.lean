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
import Mathlib

/-!
# A piecewise-linear potential

`Vpl C W` is the maximum of 16 linear functions `la i * C + lb i * W` with rational coefficients.
It is subadditive (`Vpl_add`, `Vpl_list_sum`), and one oracle call lowers `t * Vpl` by at most the
branch weight it is charged (`Vpl_query`, for `t ≥ 256`). `g1 = 12092057 / 20000000` is its value
bound at the start (`g1_le_Vpl_one`), and `g1_bound` gives `3 / 5 ≤ g1 * (1 - 2 / N)` for
`N ≥ 2 ^ 16`.
-/

namespace GroverThreeFifths

/-- slopes a_i -/
noncomputable def la : Fin 16 → ℝ := ![4961/10000, 2683/5000, 583/1000, 6367/10000, 3497/5000,
  1547/2000, 4311/5000, 9707/10000, 2213/2000, 12797/10000, 7557/5000, 3663/2000, 23103/10000,
  30813/10000, 9119/2000, 88047/10000]

/-- intercepts b_i -/
noncomputable def lb : Fin 16 → ℝ := ![0, -559953/20000000, -6342869/100000000,
  -5358367/50000000, -8034403/50000000, -11312587/50000000, -30697761/100000000,
  -20399013/50000000, -26835933/50000000, -35165987/50000000, -46440509/50000000,
  -124318039/100000000, -171671359/100000000, -248308759/100000000, -395744427/100000000,
  -164001943/20000000]

/-- breakpoints rho_i -/
noncomputable def rho : Fin 16 → ℝ := ![0, 6913/10000, 1909/2500, 1629/2000, 1067/1250, 553/625,
  9101/10000, 9309/10000, 237/250, 9619/10000, 2433/2500, 9821/10000, 989/1000, 497/500,
  4987/5000, 4997/5000]

/-- u_i = 1/(4 a_i) - 1/256 -/
noncomputable def uu (i : Fin 16) : ℝ := 1 / (4 * la i) - 1 / 256

noncomputable def Vpl (C W : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 16 => la i * C + lb i * W)
noncomputable def g1 : ℝ := 12092057 / 20000000

/-! ### Table facts -/

lemma la_pos (i : Fin 16) : 0 < la i := by
  fin_cases i <;> norm_num [la]

lemma lb_nonpos (i : Fin 16) : lb i ≤ 0 := by
  fin_cases i <;> norm_num [lb]

lemma uu_nonneg (i : Fin 16) : 0 ≤ uu i := by
  fin_cases i <;> norm_num [uu, la]

lemma line_le_g1 (i : Fin 16) : la i + lb i ≤ g1 := by
  fin_cases i <;> norm_num [la, lb, g1]

lemma uu_zero : (1 : ℝ) / 4 ≤ uu 0 ^ 2 := by
  norm_num [uu, la]

lemma step_fact (k : Fin 15) :
    la k.castSucc < la k.succ ∧ lb k.castSucc - lb k.succ = (la k.succ - la k.castSucc) * rho k.succ
    ∧ 1 / 2 ≤ rho k.succ ∧ rho k.succ ≤ 1 ∧ rho k.succ * (1 - rho k.succ) ≤ uu k.succ ^ 2 := by
  fin_cases k <;> norm_num [la, lb, rho, uu]

lemma aux_ge (a a' b b' r C W : ℝ) (ha : a' < a) (hb : b' - b = (a - a') * r)
    (h : a' * C + b' * W ≤ a * C + b * W) : r * W ≤ C := by
  by_contra hc
  have hc := not_le.1 hc
  have hbW : (b' - b) * W = (a - a') * r * W := by rw [hb]
  nlinarith [mul_pos (sub_pos.2 ha) (sub_pos.2 hc)]

lemma aux_q (r u C W : ℝ) (hr : 1 / 2 ≤ r) (hr1 : r ≤ 1) (hu : r * (1 - r) ≤ u ^ 2)
    (hW : 0 ≤ W) (hC : r * W ≤ C) (hCW : C ≤ W) : C * (W - C) ≤ u ^ 2 * W ^ 2 := by
  have h1 : (1 - r) * W ≤ C := by nlinarith
  have h2 : 0 ≤ (C - r * W) * (C - (1 - r) * W) :=
    mul_nonneg (by linarith) (by linarith)
  have h3 : r * (1 - r) * W ^ 2 ≤ u ^ 2 * W ^ 2 :=
    mul_le_mul_of_nonneg_right hu (sq_nonneg W)
  nlinarith

lemma qbound (i : Fin 16) (C W : ℝ) (hCW : C ≤ W) (hC : 0 ≤ C)
    (hmax : ∀ j : Fin 16, la j * C + lb j * W ≤ la i * C + lb i * W) :
    C * (W - C) ≤ uu i ^ 2 * W ^ 2 := by
  have hW : 0 ≤ W := le_trans hC hCW
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
  · have h := uu_zero
    have h0 : 0 ≤ W ^ 2 := sq_nonneg W
    nlinarith [sq_nonneg (C - W / 2), mul_le_mul_of_nonneg_right h h0]
  · obtain ⟨h1, h2, h3, h4, h5⟩ := step_fact k
    exact aux_q _ _ C W h3 h4 h5 hW (aux_ge _ _ _ _ _ C W h1 h2 (hmax _)) hCW

/-! ### Required statements -/

theorem Vpl_add (C₁ W₁ C₂ W₂ : ℝ) : Vpl (C₁ + C₂) (W₁ + W₂) ≤ Vpl C₁ W₁ + Vpl C₂ W₂ := by
  unfold Vpl
  apply Finset.sup'_le
  intro i hi
  have h1 : la i * C₁ + lb i * W₁ ≤
      Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 16 => la i * C₁ + lb i * W₁) :=
    Finset.le_sup' (fun i : Fin 16 => la i * C₁ + lb i * W₁) hi
  have h2 : la i * C₂ + lb i * W₂ ≤
      Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 16 => la i * C₂ + lb i * W₂) :=
    Finset.le_sup' (fun i : Fin 16 => la i * C₂ + lb i * W₂) hi
  nlinarith

theorem Vpl_zero : Vpl 0 0 = 0 := by
  unfold Vpl
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    simp
  · simp

theorem Vpl_list_sum {α : Type*} (L : List α) (C W : α → ℝ) :
    Vpl (L.map C).sum (L.map W).sum ≤ (L.map fun o => Vpl (C o) (W o)).sum := by
  induction L with
  | nil => simp [Vpl_zero]
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact le_trans (Vpl_add _ _ _ _) (add_le_add_right ih _)

theorem Vpl_query (t C W C' : ℝ) (ht : 256 ≤ t) (hC : 0 ≤ C) (hCW : C ≤ W) (hC' : 0 ≤ C')
    (h : (1 - 2 / t ^ 2) * Real.sqrt C - 2 / t * Real.sqrt (W - C) ≤ Real.sqrt C') :
    t * Vpl C W - W ≤ t * Vpl C' W := by
  have htpos : 0 < t := by linarith
  have hW : 0 ≤ W := le_trans hC hCW
  set s := Real.sqrt C with hs
  set d := Real.sqrt (W - C) with hd
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = C := Real.sq_sqrt hC
  have hs'2 : Real.sqrt C' ^ 2 = C' := Real.sq_sqrt hC'
  have hs'0 : 0 ≤ Real.sqrt C' := Real.sqrt_nonneg _
  -- Step 1
  set Δ : ℝ := 2 / t ^ 2 * s + 2 / t * d with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  have hsΔ : s - Δ ≤ Real.sqrt C' := by
    have : s - Δ = (1 - 2 / t ^ 2) * s - 2 / t * d := by rw [hΔ]; ring
    rw [this]; exact h
  have hC1 : C - 2 * s * Δ ≤ C' := by
    by_cases hc : Δ ≤ s
    · have h0 : 0 ≤ s - Δ := by linarith
      have : (s - Δ) ^ 2 ≤ Real.sqrt C' ^ 2 := pow_le_pow_left₀ h0 hsΔ 2
      nlinarith
    · have hc := not_le.1 hc
      nlinarith [mul_nonneg hs0 hs0, mul_le_mul_of_nonneg_left hc.le hs0]
  -- Step 2
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin 16 => la i * C + lb i * W) Finset.univ_nonempty
  have hmax : ∀ j : Fin 16, la j * C + lb j * W ≤ la i * C + lb i * W :=
    fun j => hi j (Finset.mem_univ j)
  have hVle : Vpl C W ≤ la i * C + lb i * W := by
    unfold Vpl
    exact Finset.sup'_le _ _ (fun j _ => hmax j)
  have hVC' : la i * C' + lb i * W ≤ Vpl C' W := by
    unfold Vpl
    exact Finset.le_sup' (fun i : Fin 16 => la i * C' + lb i * W) (Finset.mem_univ i)
  -- Step 3, 4
  have hq := qbound i C W hCW hC hmax
  have hsd : s * d ≤ uu i * W := by
    have : s * d = Real.sqrt (C * (W - C)) := by
      rw [hs, hd, Real.sqrt_mul hC]
    rw [this]
    rw [Real.sqrt_le_iff]
    refine ⟨mul_nonneg (uu_nonneg i) hW, ?_⟩
    nlinarith
  have hCt : C / t ≤ W / 256 := by
    rw [div_le_div_iff₀ htpos (by norm_num)]
    nlinarith
  -- Step 5
  have ha := la_pos i
  have hu : 4 * la i * uu i = 1 - la i / 64 := by
    unfold uu; field_simp; ring
  have hE : t * la i * (2 * s * Δ) ≤ W := by
    have e : t * la i * (2 * s * Δ) = 4 * la i * (C / t + s * d) := by
      rw [hΔ]; field_simp; rw [← hs2]; ring
    rw [e]
    have : 4 * la i * (C / t + s * d) ≤ 4 * la i * (W / 256 + uu i * W) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e2 : 4 * la i * (W / 256 + uu i * W) = W := by
      have : 4 * la i * (W / 256 + uu i * W) = la i * W / 64 + (4 * la i * uu i) * W := by ring
      rw [this, hu]; ring
    linarith
  -- Step 6
  have h6 : t * (la i * C + lb i * W) - t * la i * (2 * s * Δ) ≤ t * (la i * C' + lb i * W) := by
    have : la i * (C - 2 * s * Δ) ≤ la i * C' := mul_le_mul_of_nonneg_left hC1 ha.le
    nlinarith
  have h7 : t * Vpl C W ≤ t * (la i * C + lb i * W) := mul_le_mul_of_nonneg_left hVle htpos.le
  have h8 : t * (la i * C' + lb i * W) ≤ t * Vpl C' W := mul_le_mul_of_nonneg_left hVC' htpos.le
  linarith

theorem g1_le_Vpl_one : g1 ≤ Vpl 1 1 := by
  have := Finset.le_sup' (fun i : Fin 16 => la i * 1 + lb i * 1) (Finset.mem_univ 15)
  unfold Vpl
  refine le_trans ?_ this
  norm_num [la, lb, g1]

theorem Vpl_le (C W : ℝ) (hC : 0 ≤ C) (hCW : C ≤ W) : Vpl C W ≤ g1 * C := by
  unfold Vpl
  apply Finset.sup'_le
  intro i _
  have h1 := line_le_g1 i
  have h2 := lb_nonpos i
  nlinarith [mul_le_mul_of_nonneg_right h1 hC, mul_nonneg (neg_nonneg.2 h2) (sub_nonneg.2 hCW)]

theorem g1_bound (N : ℝ) (hN : 2 ^ 16 ≤ N) : 3 / 5 ≤ g1 * (1 - 2 / N) := by
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (by norm_num) hN
  have h : 2 / N ≤ 2 / 2 ^ 16 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN
  have : g1 * (1 - 2 / 2 ^ 16) ≤ g1 * (1 - 2 / N) := by
    apply mul_le_mul_of_nonneg_left (by linarith)
    unfold g1; norm_num
  refine le_trans ?_ this
  unfold g1; norm_num

end GroverThreeFifths

#print axioms GroverThreeFifths.Vpl_add
#print axioms GroverThreeFifths.Vpl_zero
#print axioms GroverThreeFifths.Vpl_list_sum
#print axioms GroverThreeFifths.Vpl_query
#print axioms GroverThreeFifths.g1_le_Vpl_one
#print axioms GroverThreeFifths.Vpl_le
#print axioms GroverThreeFifths.g1_bound
