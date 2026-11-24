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
module

public import QuantumComputation.QuantumHoareLogic.ResourceCounting.CostBounds
public import QuantumComputation.Circuits.DynamicCircuit
public import QuantumComputation.Primitives.Phase
public import QuantumComputation.QuantumHoareLogic.WP
public import QuantumComputation.Algorithms.QFT.States
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Phase Estimation Specification

Query-model specification for estimating an unknown phase `θ ∈ ℝ` (defined modulo `1`) given
black-box access to the single-qubit phase oracle `diag(1, exp(2πiθ))`. This is the oracle a
controlled-`U` presents to its control qubit when the target register holds an eigenvector of `U`
with eigenvalue `exp(2πiθ)` (phase kickback), so it is the eigenstate-supplied form of quantum
phase estimation (A. Kitaev, arXiv:quant-ph/9511026; R. Cleve, A. Ekert, C. Macchiavello,
M. Mosca, Proc. R. Soc. A 454, 339 (1998)).

For every precision `m` and confidence parameter `k`, the program is an adaptive dynamic circuit
(mid-circuit measurements, `.qIf`, and `.qWhile` allowed) that starts from all qubits reset and
writes an integer `res` such that `res / 2 ^ m` is within `1 / 2 ^ m` of `θ` modulo `1`, with
probability at least `1 - 1 / 2 ^ k`, for every real `θ` (runs that never terminate count as
failures; for `k = 0` the condition is empty, and `m ≤ 1` needs no oracle call). Qubit count,
non-oracle unitaries and classical conditions are free.

The resource metric is the expected number of oracle calls, evaluated semantically on the compiled
program via `CostModel.ofEmbeddedOracle`, charging `1` per oracle call and `0` for all other
operations (except any unitary step whose matrix happens to coincide with an embedded oracle call,
for example the identity when `θ` is an integer; see `CostModel.ofEmbeddedOracle`; use `.skip`
and fused steps to avoid it). The claimed bound is `phaseEstRelCost * 2 ^ m * (k + 1)`,
uniformly in `m`, `k` and `θ`, so a solution competes on the constant `phaseEstRelCost` in front
of the Heisenberg-limited scaling `2 ^ m * log (1 / δ)`.
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator ResourceCounting Real
open scoped NNReal NNRat

/-- By default we allow only a single variable. -/
inductive PhaseEst.Var where | res deriving DecidableEq, Inhabited

open PhaseEst (Var)
open PhaseEst.Var (res)

/-- Single-qubit phase oracle `diag(1, exp(2πiθ))`: `|0⟩ ↦ |0⟩`, `|1⟩ ↦ exp(2πiθ)|1⟩`. -/
noncomputable def phaseOracle (θ : ℝ) : Unitary (2 ^ 1) :=
  diagPhaseUnitary fun b : Fin (2 ^ 1) ↦ if b = 0 then 0 else θ

/-- The integer `y` is an `m`-bit estimate of `θ`: `y / 2 ^ m` is within `1 / 2 ^ m` of `θ`
modulo `1`. -/
def IsPhaseEstimate (m : ℕ) (θ : ℝ) (y : ℤ) : Prop :=
  ∃ j : ℤ, |θ - (y : ℝ) / (2 : ℝ) ^ m - (j : ℝ)| ≤ 1 / (2 : ℝ) ^ m

/-! ## Baseline: coherent majority vote (helpers)

`6 * (k + 1)` independent runs of `(m + 3)`-bit phase estimation, a fused inverse Fourier transform
plus vote step, and a measurement of the output register. Proved in
a separate working file (not published here); copied here under a separate namespace. -/

namespace PhaseEstBaselineGeneral

open scoped Matrix

open QProg.Notation

/-! ## The circuit -/
/-- The Fourier transform on `m` qubits, from the library. -/
noncomputable def qftU (m : ℕ) : Unitary (2 ^ m) := QFT.qftUnitary m

/-- The inverse Fourier transform. -/
noncomputable def iqftU (m : ℕ) : Unitary (2 ^ m) := star (qftU m)

lemma qftU_val (m : ℕ) : (qftU m).1 = QFT.qftMatrix m := QFT.val_qftUnitary m

lemma iqftU_val (m : ℕ) : (iqftU m).1 = star (QFT.qftMatrix m) := by
  show star (qftU m).1 = _
  rw [qftU_val]

/-- The wires of the oracle calls: wire `j` is called `2 ^ j` times. -/
def oracleCalls (m : ℕ) : List (Fin m) :=
  (List.finRange m).flatMap fun j ↦ List.replicate (2 ^ j.val) j

/-- Oracle calls on the listed wires, in order. -/
noncomputable def oracleBlock {m : ℕ} (l : List (Fin m)) :
    OracleDynamicCircuit (Unitary (2 ^ m)) Var m 1 :=
  OracleDynamicCircuit.sequence
    (l.map fun j ↦ OracleDynamicCircuit.oracle (QRegister.singleton j))

/-- The oracle embedded on wire `j`. -/
noncomputable def oraU (θ : ℝ) {m : ℕ} (j : Fin m) : Unitary (2 ^ m) :=
  (QRegister.singleton j).embedUnitary (phaseOracle θ)

/-- The compiled oracle block. -/
noncomputable def blockProg (θ : ℝ) {m : ℕ} : List (Fin m) → QProg Var (2 ^ m)
  | [] => QProg.skip
  | j :: l => QProg.qSeq (QProg.qAssign (oraU θ j)) (blockProg θ l)

lemma compile_block (θ : ℝ) {m : ℕ} (l : List (Fin m)) :
    (oracleBlock l).compile QProg.qAssign (phaseOracle θ) = blockProg θ l := by
  induction l with
  | nil => rfl
  | cons j l ih => exact congrArg (QProg.qSeq (QProg.qAssign (oraU θ j))) ih
lemma block_cost (θ : ℝ) {m : ℕ} (l : List (Fin m)) :
    CostBound (CostModel.ofEmbeddedOracle (phaseOracle θ)) (blockProg θ l : QProg Var (2 ^ m))
      (l.length : ℝ≥0) := by
  induction l with
  | nil => simpa [blockProg] using CostBound.skip_zero (Var := Var) _
  | cons j l ih =>
    have h := CostBound.seq
      (CostBound.qAssign (Var := Var) (CostModel.ofEmbeddedOracle (phaseOracle θ)) (oraU θ j)) ih
    refine CostBound.mono h (le_of_eq ?_)
    simp [oraU, add_comm]
lemma geom_two (m : ℕ) : ∑ i ∈ Finset.range m, 2 ^ i + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, pow_succ]; omega

lemma length_flatMap_replicate {m : ℕ} (c : Fin m → ℕ) (l : List (Fin m)) :
    (l.flatMap fun j ↦ List.replicate (c j) j).length = (l.map c).sum := by
  induction l with
  | nil => simp
  | cons j l ih => simp [List.flatMap_cons, ih]

lemma oracleCalls_length (m : ℕ) : (oracleCalls m).length + 1 = 2 ^ m := by
  unfold oracleCalls
  rw [length_flatMap_replicate (fun j : Fin m ↦ 2 ^ j.val), ← Fin.sum_univ_def,
    Fin.sum_univ_eq_sum_range (fun i ↦ 2 ^ i) m]
  exact geom_two m
/-! ## Oracle matrices -/

/-- `exp(2πiθ)`. -/
noncomputable def phaseZ (θ : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * (θ : ℂ))

/-- The bit of the basis index `g` on wire `j`. -/
def bitN {m : ℕ} (j : Fin m) (g : Fin (2 ^ m)) : ℕ := g.val / 2 ^ j.val % 2

lemma extract_val {m : ℕ} (j : Fin m) (g : Fin (2 ^ m)) :
    (((QRegister.singleton j).extractIndex g : Fin (2 ^ 1)) : ℕ) = bitN j g := by
  have h := QRegister.basisBits_extractIndex (QRegister.singleton j) g 0
  rw [QRegister.singleton_apply, basisBits_eq_div_mod, basisBits_eq_div_mod] at h
  have h2 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h
  have hlt := ((QRegister.singleton j).extractIndex g).isLt
  simp only [Fin.val_zero, pow_zero, Nat.div_one, Nat.mod_mod, pow_one] at h2 hlt
  unfold bitN
  rw [← h2]
  exact (Nat.mod_eq_of_lt hlt).symm

lemma oraU_val (θ : ℝ) {m : ℕ} (j : Fin m) :
    (oraU θ j).1 = Matrix.diagonal (fun g : Fin (2 ^ m) ↦ phaseZ θ ^ bitN j g) := by
  show (QRegister.singleton j).embedMatrix (Matrix.diagonal _) = _
  rw [QRegister.embedMatrix_diagonal]
  congr 1
  funext g
  have hv := extract_val j g
  have hb : bitN j g = 0 ∨ bitN j g = 1 := Nat.mod_two_eq_zero_or_one _
  rcases hb with hb | hb
  · have he : (QRegister.singleton j).extractIndex g = 0 := Fin.ext (by rw [hv, hb]; rfl)
    rw [he, hb]
    simp
  · have he : (QRegister.singleton j).extractIndex g ≠ 0 := by
      intro h0
      rw [h0] at hv
      rw [hb] at hv
      exact absurd hv (by simp)
    rw [hb]
    simp [he, phaseZ]

/-- The diagonal matrix of a list of oracle calls. -/
noncomputable def blockMat (θ : ℝ) {m : ℕ} (l : List (Fin m)) :
    Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ :=
  Matrix.diagonal fun g ↦ phaseZ θ ^ (l.map fun j ↦ bitN j g).sum

lemma blockMat_cons (θ : ℝ) {m : ℕ} (j : Fin m) (l : List (Fin m)) :
    blockMat θ (j :: l) = blockMat θ l * (oraU θ j).1 := by
  rw [oraU_val, blockMat, blockMat, Matrix.diagonal_mul_diagonal]
  congr 1
  funext g
  simp [pow_add, mul_comm]

lemma block_wp_mat (θ : ℝ) {m : ℕ} (l : List (Fin m)) (Θ : CQAssertion (Store Var) (2 ^ m))
    (σ : Store Var) :
    ((wp (blockProg θ l) Θ) σ).1.mat =
      star (blockMat θ l) * (Θ σ).1.mat * blockMat θ l := by
  induction l with
  | nil => simp [blockProg, blockMat, wp_skip]
  | cons j l ih =>
    simp only [blockProg, wp_qSeq, wp_qAssign]
    rw [CQAssertion.qAssign_apply_mat, ih, blockMat_cons, star_mul]
    simp only [Matrix.star_eq_conjTranspose, Matrix.mul_assoc]

lemma sum_bits (m : ℕ) : ∀ g : ℕ, g < 2 ^ m → ∑ i : Fin m, 2 ^ i.val * (g / 2 ^ i.val % 2) = g := by
  induction m with
  | zero => intro g hg; simp at hg; simp [hg]
  | succ m ih =>
    intro g hg
    rw [Fin.sum_univ_succ]
    have hg2 : g / 2 < 2 ^ m := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]
      rw [pow_succ] at hg
      omega
    have key : ∀ i : Fin m, 2 ^ (i.succ).val * (g / 2 ^ (i.succ).val % 2) =
        2 * (2 ^ i.val * (g / 2 / 2 ^ i.val % 2)) := by
      intro i
      rw [Fin.val_succ, pow_succ', Nat.div_div_eq_div_mul]
      ring
    simp only [key, ← Finset.mul_sum]
    rw [ih _ hg2]
    simp
    omega

lemma sum_flatMap_replicate {m : ℕ} (c : Fin m → ℕ) (f : Fin m → ℕ) (l : List (Fin m)) :
    ((l.flatMap fun j ↦ List.replicate (c j) j).map f).sum = (l.map fun j ↦ c j * f j).sum := by
  induction l with
  | nil => simp
  | cons j l ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

lemma sum_oracleCalls (m : ℕ) (g : Fin (2 ^ m)) :
    ((oracleCalls m).map fun j ↦ bitN j g).sum = g.val := by
  unfold oracleCalls
  rw [sum_flatMap_replicate (fun j : Fin m ↦ 2 ^ j.val) (fun j ↦ bitN j g),
    ← Fin.sum_univ_def]
  exact sum_bits m g.val g.isLt
/-! ## Amplitudes -/

/-- The whole unitary `iqft · O · qft` on the phase oracle block. -/
noncomputable def Wm (m : ℕ) (θ : ℝ) : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ :=
  star (QFT.qftMatrix m) * Matrix.diagonal (fun g : Fin (2 ^ m) ↦ phaseZ θ ^ g.val) *
    QFT.qftMatrix m

/-- `(1/N) ∑_{x<N} exp(2πi x δ / N)`. -/
noncomputable def ampG (N : ℕ) (δ : ℝ) : ℂ :=
  (1 / (N : ℂ)) * ∑ x ∈ Finset.range N,
    Complex.exp (2 * π * Complex.I * (((x : ℝ) * δ / N : ℝ) : ℂ))

lemma exp_mul_aux (r A B : ℂ) :
    r * Complex.exp A * Complex.exp B * r = r * r * Complex.exp (A + B) := by
  rw [Complex.exp_add]; ring

lemma term_eq (m : ℕ) (θ : ℝ) (x y : Fin (2 ^ m)) :
    star (QFT.qftMatrix m x y) * phaseZ θ ^ x.val * QFT.qftMatrix m x 0 =
      (1 / (((2 ^ m : ℕ)) : ℂ)) * Complex.exp (2 * π * Complex.I *
        (((x.val : ℝ) * ((2 : ℝ) ^ m * θ - (y.val : ℝ)) / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ)) := by
  have hN : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hr2 : ((√((2 : ℝ) ^ m) : ℝ) : ℂ) * ((√((2 : ℝ) ^ m) : ℝ) : ℂ) = (2 : ℂ) ^ m := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hN.le]; push_cast; rfl
  have hstar : ∀ z : ℂ, star (Complex.exp z) = Complex.exp (star z) := by
    intro z
    simp only [Complex.star_def]
    exact (Complex.exp_conj z).symm
  have e1 : (1 / (((2 ^ m : ℕ)) : ℂ)) = (1 / ((√((2 : ℝ) ^ m) : ℝ) : ℂ)) *
      (1 / ((√((2 : ℝ) ^ m) : ℝ) : ℂ)) := by
    rw [one_div_mul_one_div, hr2]; push_cast; rfl
  have hr : ((√((2 : ℝ) ^ m) : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; exact (Real.sqrt_pos.2 hN).ne'
  have h2m : ((2 : ℂ) ^ m) ≠ 0 := pow_ne_zero _ two_ne_zero
  unfold QFT.qftMatrix
  rw [star_mul', hstar, phaseZ, ← Complex.exp_nat_mul]
  simp only [Fin.val_zero, Nat.cast_zero, zero_mul, zero_div, mul_zero, Complex.exp_zero,
    Complex.ofReal_zero, mul_one]
  have hs1 : star (1 / ((√((2 : ℝ) ^ m) : ℝ) : ℂ)) = 1 / ((√((2 : ℝ) ^ m) : ℝ) : ℂ) := by
    simp [Complex.star_def]
  rw [hs1, exp_mul_aux, e1]
  congr 1
  congr 1
  simp only [Complex.star_def, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I,
    Complex.conj_ofNat]
  push_cast
  field_simp
  ring

/-! ## Success probability: analytic part -/

lemma poly_ineq (e : ℝ) (h0 : 0 ≤ e) (h1 : e ≤ 784 / 10000) :
    (3 / 4) * (99225 / 10000) * (1 / 4 - e) ^ 2 ≤
      (1 - (99225 / 10000) / 2 * e) ^ 2 * (1 / 2 + 2 * e) := by
  nlinarith [mul_nonneg h0 (sub_nonneg.2 h1), pow_nonneg h0 3, pow_nonneg h0 2]

lemma sinc_caseB (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 22 / 100) :
    3 / 4 ≤ Real.sin (π * t) ^ 2 / (π * t) ^ 2 := by
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have ha0 : 0 < π * t := by positivity
  have ha2 : π * t ≤ 7 / 10 := by nlinarith [mul_nonneg (sub_nonneg.2 hπ.le) ht0.le]
  have ha1 : π * t ≤ 1 := by linarith
  have hs := Real.sin_gt_sub_cube ha0
  have hb : 87 / 100 ≤ 1 - (π * t) ^ 2 / 6 := by
    nlinarith [mul_nonneg ha0.le (sub_nonneg.2 ha2)]
  have hs' : 1 - (π * t) ^ 2 / 6 ≤ Real.sin (π * t) / (π * t) := by
    rw [le_div_iff₀ ha0]; nlinarith [hs]
  have hsq : (87 / 100 : ℝ) ^ 2 ≤ (Real.sin (π * t) / (π * t)) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (hb.trans hs') 2
  calc (3 / 4 : ℝ) ≤ (87 / 100) ^ 2 := by norm_num
    _ ≤ (Real.sin (π * t) / (π * t)) ^ 2 := hsq
    _ = Real.sin (π * t) ^ 2 / (π * t) ^ 2 := div_pow _ _ _

lemma sinc_caseA (t : ℝ) (ht0 : 22 / 100 ≤ t) (ht1 : t ≤ 1 / 2) :
    3 / 4 ≤ Real.sin (π * t) ^ 2 / (π * t) ^ 2 +
      Real.sin (π * (1 - t)) ^ 2 / (π * (1 - t)) ^ 2 := by
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have hsin : Real.sin (π * (1 - t)) = Real.sin (π * t) := by
    rw [show π * (1 - t) = π - π * t by ring, Real.sin_pi_sub]
  rw [hsin]
  have hcos : 1 - (π * (1 / 2 - t)) ^ 2 / 2 ≤ Real.sin (π * t) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := π * (1 / 2 - t))
    have e : Real.cos (π * (1 / 2 - t)) = Real.sin (π * t) := by
      rw [← Real.sin_pi_div_two_sub]; congr 1; ring
    rwa [e] at h
  have hP : π ^ 2 ≤ 99225 / 10000 := by nlinarith
  have hd0 : 0 ≤ 1 / 2 - t := by linarith
  have hd1 : (1 / 2 - t) ^ 2 ≤ 784 / 10000 := by
    nlinarith [mul_nonneg hd0 (show 0 ≤ 28 / 100 - (1 / 2 - t) by linarith)]
  have hc : 1 - (99225 / 10000) / 2 * (1 / 2 - t) ^ 2 ≤ 1 - (π * (1 / 2 - t)) ^ 2 / 2 := by
    rw [mul_pow]; nlinarith [mul_le_mul_of_nonneg_right hP (sq_nonneg (1 / 2 - t))]
  have hchi0 : 0 ≤ 1 - (99225 / 10000) / 2 * (1 / 2 - t) ^ 2 := by linarith
  have hs2 : (1 - (99225 / 10000) / 2 * (1 / 2 - t) ^ 2) ^ 2 ≤ Real.sin (π * t) ^ 2 :=
    pow_le_pow_left₀ hchi0 (hc.trans hcos) 2
  have key := poly_ineq ((1 / 2 - t) ^ 2) (sq_nonneg _) hd1
  have key2 : (3 / 4) * π ^ 2 * (t * (1 - t)) ^ 2 ≤
      (1 - (99225 / 10000) / 2 * (1 / 2 - t) ^ 2) ^ 2 * (t ^ 2 + (1 - t) ^ 2) := by
    have e1 : t * (1 - t) = 1 / 4 - (1 / 2 - t) ^ 2 := by ring
    have e2 : t ^ 2 + (1 - t) ^ 2 = 1 / 2 + 2 * (1 / 2 - t) ^ 2 := by ring
    rw [e1, e2]
    have h3 := mul_le_mul_of_nonneg_right hP (sq_nonneg (1 / 4 - (1 / 2 - t) ^ 2))
    nlinarith [h3]
  have ht : 0 < t := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hX : 0 < (π * t) ^ 2 := by positivity
  have hY : 0 < (π * (1 - t)) ^ 2 := by positivity
  have hstep : (1 - (99225 / 10000) / 2 * (1 / 2 - t) ^ 2) ^ 2 / (π * t) ^ 2 +
      (1 - (99225 / 10000) / 2 * (1 / 2 - t) ^ 2) ^ 2 / (π * (1 - t)) ^ 2 ≤
      Real.sin (π * t) ^ 2 / (π * t) ^ 2 + Real.sin (π * t) ^ 2 / (π * (1 - t)) ^ 2 := by
    gcongr
  refine le_trans ?_ hstep
  rw [div_add_div _ _ hX.ne' hY.ne', le_div_iff₀ (mul_pos hX hY)]
  have h4 := mul_le_mul_of_nonneg_left key2 (sq_nonneg π)
  nlinarith [h4]

/-- The inequality on `(0, 1/2]`. -/
lemma sinc_pair_half (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) :
    3 / 4 ≤ Real.sin (π * t) ^ 2 / (π * t) ^ 2 +
      Real.sin (π * (1 - t)) ^ 2 / (π * (1 - t)) ^ 2 := by
  by_cases h : t ≤ 22 / 100
  · have h1 := sinc_caseB t ht0 h
    have h2 : 0 ≤ Real.sin (π * (1 - t)) ^ 2 / (π * (1 - t)) ^ 2 := by positivity
    linarith
  · exact sinc_caseA t (not_le.1 h).le ht1

/-! ## Amplitudes: the Dirichlet kernel -/

lemma normSq_exp_sub_one (a : ℝ) :
    Complex.normSq (Complex.exp ((a : ℂ) * Complex.I) - 1) = 4 * Real.sin (a / 2) ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.one_re, Complex.one_im]
  have h : Real.cos a = 1 - 2 * Real.sin (a / 2) ^ 2 := by
    have h0 := Real.cos_two_mul (a / 2)
    rw [show 2 * (a / 2) = a by ring] at h0
    rw [h0]; nlinarith [Real.sin_sq_add_cos_sq (a / 2)]
  linear_combination Real.sin_sq_add_cos_sq a - 2 * h

lemma amp_final (n s1 s2 N : ℝ) (hN : N ≠ 0) (h : 4 * s1 * n = 4 * s2) :
    1 / N ^ 2 * n * (N ^ 2 * s1) = s2 := by
  have e : 1 / N ^ 2 * n * (N ^ 2 * s1) = s1 * n := by field_simp
  rw [e]; linarith

lemma ampG_key (N : ℕ) (hN : 0 < N) (δ : ℝ) :
    Complex.normSq (ampG N δ) * ((N : ℝ) ^ 2 * Real.sin (π * δ / N) ^ 2) =
      Real.sin (π * δ) ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hterm : ∀ x : ℕ, Complex.exp (2 * π * Complex.I * (((x : ℝ) * δ / N : ℝ) : ℂ)) =
      Complex.exp (((2 * π * δ / N : ℝ) : ℂ) * Complex.I) ^ x := by
    intro x
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hS : ampG N δ = (1 / (N : ℂ)) * ∑ x ∈ Finset.range N,
      Complex.exp (((2 * π * δ / N : ℝ) : ℂ) * Complex.I) ^ x := by
    unfold ampG; simp only [hterm]
  have hwN : Complex.exp (((2 * π * δ / N : ℝ) : ℂ) * Complex.I) ^ N =
      Complex.exp (((2 * π * δ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    first | (field_simp; done) | (field_simp; ring)
  have hgeom := mul_geom_sum (Complex.exp (((2 * π * δ / N : ℝ) : ℂ) * Complex.I)) N
  have h1 := congrArg Complex.normSq hgeom
  rw [Complex.normSq_mul, hwN, normSq_exp_sub_one, normSq_exp_sub_one] at h1
  have e1 : 2 * π * δ / N / 2 = π * δ / N := by ring
  have e2 : 2 * π * δ / 2 = π * δ := by ring
  rw [e1, e2] at h1
  have hn : Complex.normSq (1 / (N : ℂ)) = 1 / (N : ℝ) ^ 2 := by
    rw [show (1 / (N : ℂ)) = ((1 / N : ℝ) : ℂ) by push_cast; ring, Complex.normSq_ofReal]
    ring
  rw [hS, Complex.normSq_mul, hn]
  exact amp_final _ _ _ _ hNr.ne' h1

lemma ampG_lower (N : ℕ) (hN : 0 < N) (δ : ℝ) :
    Real.sin (π * δ) ^ 2 ≤ Complex.normSq (ampG N δ) * (π * δ) ^ 2 := by
  have h := ampG_key N hN δ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hsin : Real.sin (π * δ / N) ^ 2 ≤ (π * δ / N) ^ 2 := Real.sin_sq_le_sq
  have hn := Complex.normSq_nonneg (ampG N δ)
  have e : (N : ℝ) ^ 2 * (π * δ / N) ^ 2 = (π * δ) ^ 2 := by field_simp
  calc Real.sin (π * δ) ^ 2 = _ := h.symm
    _ ≤ Complex.normSq (ampG N δ) * ((N : ℝ) ^ 2 * (π * δ / N) ^ 2) := by gcongr
    _ = _ := by rw [e]

lemma ampG_ge (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ : δ ≠ 0) :
    Real.sin (π * δ) ^ 2 / (π * δ) ^ 2 ≤ Complex.normSq (ampG N δ) := by
  have hp : 0 < (π * δ) ^ 2 := by positivity
  rw [div_le_iff₀ hp]
  exact ampG_lower N hN δ

lemma ampG_zero (N : ℕ) (hN : 0 < N) : ampG N 0 = 1 := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold ampG
  simp [hNc]

lemma ampG_periodic (N : ℕ) (hN : 0 < N) (δ : ℝ) (k : ℤ) :
    ampG N (δ + N * k) = ampG N δ := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have e : ∀ x : ℕ, 2 * π * Complex.I * (((x : ℝ) * (δ + N * k) / N : ℝ) : ℂ) =
      2 * π * Complex.I * (((x : ℝ) * δ / N : ℝ) : ℂ) +
        ((x * k : ℤ) : ℂ) * (2 * π * Complex.I) := by
    intro x
    push_cast
    first | (field_simp; done) | (field_simp; ring)
  unfold ampG
  congr 1
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ## Outcomes -/

lemma Wm_apply (m : ℕ) (θ : ℝ) (y : Fin (2 ^ m)) :
    Wm m θ y 0 = ampG (2 ^ m) ((2 : ℝ) ^ m * θ - (y.val : ℝ)) := by
  unfold Wm
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.star_apply, term_eq]
  unfold ampG
  rw [← Finset.mul_sum]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun x : ℕ ↦ Complex.exp (2 * π * Complex.I *
    (((x : ℝ) * ((2 : ℝ) ^ m * θ - (y.val : ℝ)) / ((2 ^ m : ℕ) : ℝ) : ℝ) : ℂ))) (2 ^ m)

/-- The outcome of `Fin N` congruent to the integer `a` modulo `N`. -/
def ofIntN (N : ℕ) (hN : 0 < N) (a : ℤ) : Fin N :=
  ⟨(a % (N : ℤ)).toNat, by
    have h0 : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
    have h1 := Int.emod_lt_of_pos a h0
    have h2 := Int.emod_nonneg a h0.ne'
    omega⟩

lemma ofIntN_val (N : ℕ) (hN : 0 < N) (a : ℤ) :
    (((ofIntN N hN a).val : ℕ) : ℤ) = a - N * (a / N) := by
  have h2 := Int.emod_nonneg a (by exact_mod_cast hN.ne' : (N : ℤ) ≠ 0)
  show (((a % (N : ℤ)).toNat : ℕ) : ℤ) = _
  rw [Int.toNat_of_nonneg h2, Int.emod_def]

lemma ofIntN_ne (N : ℕ) (hN : 0 < N) (hN1 : 1 < N) (a : ℤ) :
    ofIntN N hN a ≠ ofIntN N hN (a + 1) := by
  intro h
  have h' : (a % (N : ℤ)).toNat = ((a + 1) % (N : ℤ)).toNat := congrArg Fin.val h
  have h0 : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
  have n1 := Int.emod_nonneg a h0.ne'
  have n2 := Int.emod_nonneg (a + 1) h0.ne'
  have h3 : (a + 1) % (N : ℤ) = a % (N : ℤ) := by omega
  have h5 := (Int.emod_eq_emod_iff_emod_sub_eq_zero.1 h3)
  rw [show a + 1 - a = 1 by ring, Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast hN1)] at h5
  exact one_ne_zero h5

/-- The outcome of `Fin (2 ^ m)` congruent to `a`. -/
def ofInt (m : ℕ) (a : ℤ) : Fin (2 ^ m) := ofIntN (2 ^ m) (Nat.two_pow_pos m) a

lemma ofInt_val (m : ℕ) (a : ℤ) :
    ∃ q : ℤ, (((ofInt m a).val : ℕ) : ℝ) = (a : ℝ) - (2 : ℝ) ^ m * q := by
  refine ⟨a / ((2 ^ m : ℕ) : ℤ), ?_⟩
  have h := ofIntN_val (2 ^ m) (Nat.two_pow_pos m) a
  have h' : ((((ofInt m a).val : ℕ) : ℤ) : ℝ) =
      ((a - ((2 ^ m : ℕ) : ℤ) * (a / ((2 ^ m : ℕ) : ℤ)) : ℤ) : ℝ) := by
    rw [show (ofInt m a).val = (ofIntN (2 ^ m) (Nat.two_pow_pos m) a).val from rfl, h]
  push_cast at h' ⊢
  linarith

lemma amp_ofInt (m : ℕ) (θ : ℝ) (a : ℤ) :
    Wm m θ (ofInt m a) 0 = ampG (2 ^ m) ((2 : ℝ) ^ m * θ - a) := by
  obtain ⟨q, hq⟩ := ofInt_val m a
  rw [Wm_apply, hq]
  have h := ampG_periodic (2 ^ m) (Nat.two_pow_pos m) ((2 : ℝ) ^ m * θ - a) q
  rw [← h]
  congr 1
  push_cast
  ring

lemma isPE_ofInt (m : ℕ) (θ : ℝ) (a : ℤ) (h : |(2 : ℝ) ^ m * θ - a| ≤ 1) :
    IsPhaseEstimate m θ (((ofInt m a).val : ℕ) : ℤ) := by
  have hN : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  obtain ⟨q, hq⟩ := ofInt_val m a
  refine ⟨q, ?_⟩
  rw [Int.cast_natCast, hq]
  have e : θ - ((a : ℝ) - (2 : ℝ) ^ m * q) / (2 : ℝ) ^ m - q = ((2 : ℝ) ^ m * θ - a) / (2 : ℝ) ^ m := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos hN]
  exact div_le_div_of_nonneg_right h hN.le

open scoped Classical in
/-- Sum of the outcome probabilities over the good outcomes. -/
noncomputable def succM (m : ℕ) (θ : ℝ) : ℝ :=
  ∑ y : Fin (2 ^ m), if IsPhaseEstimate m θ (y.val : ℤ) then
    Complex.normSq (Wm m θ y 0) else 0

open scoped Classical in
lemma pr_ofInt_ge (m : ℕ) (θ : ℝ) (a : ℤ) (h : |(2 : ℝ) ^ m * θ - a| ≤ 1) :
    Complex.normSq (Wm m θ (ofInt m a) 0) ≤ succM m θ := by
  unfold succM
  have hg := isPE_ofInt m θ a h
  have := Finset.single_le_sum (f := fun y : Fin (2 ^ m) ↦
    if IsPhaseEstimate m θ (y.val : ℤ) then Complex.normSq (Wm m θ y 0) else 0)
    (fun y _ ↦ by
      by_cases hy : IsPhaseEstimate m θ (y.val : ℤ) <;> simp [hy, Complex.normSq_nonneg])
    (Finset.mem_univ (ofInt m a))
  simp only [if_pos hg] at this
  exact this

open scoped Classical in
lemma pair_le_succ (m : ℕ) (θ : ℝ) (y1 y2 : Fin (2 ^ m)) (hne : y1 ≠ y2)
    (h1 : IsPhaseEstimate m θ (y1.val : ℤ)) (h2 : IsPhaseEstimate m θ (y2.val : ℤ)) :
    Complex.normSq (Wm m θ y1 0) + Complex.normSq (Wm m θ y2 0) ≤ succM m θ := by
  unfold succM
  have hsub : ({y1, y2} : Finset (Fin (2 ^ m))) ⊆ Finset.univ := Finset.subset_univ _
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun y : Fin (2 ^ m) ↦
    if IsPhaseEstimate m θ (y.val : ℤ) then Complex.normSq (Wm m θ y 0) else 0)
    (fun y _ _ ↦ by
      by_cases hy : IsPhaseEstimate m θ (y.val : ℤ) <;> simp [hy, Complex.normSq_nonneg])
  simp only [Finset.sum_pair hne, if_pos h1, if_pos h2] at this
  exact this

lemma succ_ge (m : ℕ) (θ : ℝ) : 1 - 1 / (2 : ℝ) ^ 2 ≤ succM m θ := by
  have hN : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  obtain ⟨a, ha0, ha1⟩ : ∃ a : ℤ, (a : ℝ) ≤ (2 : ℝ) ^ m * θ ∧ (2 : ℝ) ^ m * θ < a + 1 :=
    ⟨⌊(2 : ℝ) ^ m * θ⌋, Int.floor_le _, Int.lt_floor_add_one _⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (2 : ℝ) ^ m * θ - a := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t < 1 := by linarith
  have hA : |(2 : ℝ) ^ m * θ - a| ≤ 1 := by
    rw [← ht, abs_of_nonneg ht0]; exact ht1.le
  have hB : |(2 : ℝ) ^ m * θ - ((a + 1 : ℤ) : ℝ)| ≤ 1 := by
    have e : (2 : ℝ) ^ m * θ - ((a + 1 : ℤ) : ℝ) = t - 1 := by push_cast; linarith
    rw [e, abs_of_nonpos (by linarith)]; linarith
  have hpa : Wm m θ (ofInt m a) 0 = ampG (2 ^ m) t := by rw [amp_ofInt, ht]
  have hpb : Wm m θ (ofInt m (a + 1)) 0 = ampG (2 ^ m) (t - 1) := by
    rw [amp_ofInt]; congr 1; push_cast; linarith
  have e : (1 : ℝ) - 1 / 2 ^ 2 = 3 / 4 := by norm_num
  rw [e]
  have hpa1 := pr_ofInt_ge m θ a hA
  rw [hpa] at hpa1
  rcases eq_or_lt_of_le ht0 with h0 | hpos
  · rw [← h0, ampG_zero _ (Nat.two_pow_pos m)] at hpa1
    simp at hpa1
    linarith
  · rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have h1 : ampG (2 ^ 0) t = 1 := by simp [ampG]
      rw [h1] at hpa1
      simp at hpa1
      linarith
    · have hne : ofInt m a ≠ ofInt m (a + 1) :=
        ofIntN_ne (2 ^ m) (Nat.two_pow_pos m) (Nat.one_lt_two_pow hm.ne') a
      have hpair := pair_le_succ m θ _ _ hne (isPE_ofInt m θ a hA) (isPE_ofInt m θ (a + 1) hB)
      rw [hpa, hpb] at hpair
      have l1 := ampG_ge (2 ^ m) (Nat.two_pow_pos m) t hpos.ne'
      have l2 := ampG_ge (2 ^ m) (Nat.two_pow_pos m) (t - 1) (sub_ne_zero.2 ht1.ne)
      have es : Real.sin (π * (t - 1)) ^ 2 / (π * (t - 1)) ^ 2 =
          Real.sin (π * (1 - t)) ^ 2 / (π * (1 - t)) ^ 2 := by
        rw [show π * (t - 1) = -(π * (1 - t)) by ring, Real.sin_neg, neg_sq, neg_sq]
      rw [es] at l2
      have key : 3 / 4 ≤ Real.sin (π * t) ^ 2 / (π * t) ^ 2 +
          Real.sin (π * (1 - t)) ^ 2 / (π * (1 - t)) ^ 2 := by
        rcases le_total t (1 / 2) with h | h
        · exact sinc_pair_half t hpos h
        · have h' := sinc_pair_half (1 - t) (by linarith) (by linarith)
          rw [sub_sub_cancel] at h'
          linarith
      linarith
open scoped Classical in
lemma entry (m : ℕ) (W : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) (g : Fin (2 ^ m) → Prop) :
    (W.conjTranspose * Matrix.diagonal (fun y ↦ if g y then (1 : ℂ) else 0) * W) 0 0 =
      ((∑ y, if g y then Complex.normSq (W y 0) else 0 : ℝ) : ℂ) := by
  rw [Matrix.mul_apply, Complex.ofReal_sum]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  split_ifs <;> simp [Complex.normSq_eq_conj_mul_self]
/-! ## Classical vote -/

/-- `a` and `b` are within `2` of each other modulo `M`. -/
def Near (M : ℕ) (a b : ℤ) : Prop := ∃ j : ℤ, |a - b - j * (M : ℤ)| ≤ 2

open Classical in
/-- The number of runs that are near run `i`. -/
noncomputable def cnt {R : ℕ} (M : ℕ) (y : Fin R → ℕ) (i : Fin R) : ℕ :=
  (Finset.univ.filter fun j ↦ Near M (y j : ℤ) (y i : ℤ)).card

open Classical in
/-- The least index satisfying the predicate, given that one exists. -/
noncomputable def leastIdx {R : ℕ} {p : Fin R → Prop} (h : ∃ i, p i) : Fin R :=
  (Finset.univ.filter p).min' (by obtain ⟨i, hi⟩ := h; exact ⟨i, by simp [hi]⟩)

open Classical in
lemma leastIdx_spec {R : ℕ} {p : Fin R → Prop} (h : ∃ i, p i) : p (leastIdx h) := by
  have hm := Finset.min'_mem (Finset.univ.filter p)
    (by obtain ⟨i, hi⟩ := h; exact ⟨i, by simp [hi]⟩)
  exact (Finset.mem_filter.1 hm).2

open Classical in
/-- The vote: the least run index with a strict majority near it, rounded to a coarser grid; else `0`. -/
noncomputable def voteVal {R : ℕ} (M : ℕ) (y : Fin R → ℕ) : ℕ :=
  if h : ∃ i, R < 2 * cnt M y i then (y (leastIdx h) + 4) / 8 else 0

theorem near_of_good (m : ℕ) (θ : ℝ) (a b : ℕ)
    (ha : IsPhaseEstimate (m + 3) θ (a : ℤ)) (hb : IsPhaseEstimate (m + 3) θ (b : ℤ)) :
    Near (2 ^ (m + 3)) (a : ℤ) (b : ℤ) := by
  obtain ⟨j1, h1⟩ := ha
  obtain ⟨j2, h2⟩ := hb
  refine ⟨j2 - j1, ?_⟩
  suffices hR : |(a : ℝ) - b - ((j2 - j1 : ℤ) : ℝ) * (((2 ^ (m + 3) : ℕ)) : ℝ)| ≤ 2 by
    exact_mod_cast hR
  have hN : (0 : ℝ) < 2 ^ (m + 3) := by positivity
  simp only [Int.cast_natCast] at h1 h2
  rw [abs_le] at h1 h2 ⊢
  push_cast
  have e1 := h1.1; have e2 := h1.2; have e3 := h2.1; have e4 := h2.2
  have hd : (1 : ℝ) / 2 ^ (m + 3) * 2 ^ (m + 3) = 1 := by field_simp
  have k1 : ((θ - (a : ℝ) / 2 ^ (m + 3) - j1) * 2 ^ (m + 3)) = θ * 2 ^ (m + 3) - a - j1 * 2 ^ (m + 3) := by
    field_simp
  have k2 : ((θ - (b : ℝ) / 2 ^ (m + 3) - j2) * 2 ^ (m + 3)) = θ * 2 ^ (m + 3) - b - j2 * 2 ^ (m + 3) := by
    field_simp
  have m1 := mul_le_mul_of_nonneg_right e1 hN.le
  have m2 := mul_le_mul_of_nonneg_right e2 hN.le
  have m3 := mul_le_mul_of_nonneg_right e3 hN.le
  have m4 := mul_le_mul_of_nonneg_right e4 hN.le
  rw [k1] at m1 m2
  rw [k2] at m3 m4
  have n1 : -(1 : ℝ) / 2 ^ (m + 3) * 2 ^ (m + 3) = -1 := by field_simp
  have n2 : -(1 / (2:ℝ) ^ (m + 3)) * 2 ^ (m + 3) = -1 := by field_simp
  rw [hd] at m2 m4
  rw [n2] at m1 m3
  have e5 : ((j2 : ℝ) - j1) * 2 ^ (m + 3) = j2 * 2 ^ (m + 3) - j1 * 2 ^ (m + 3) := by ring
  constructor <;> linarith [e5]

open scoped Classical in
theorem vote_isPE (m R : ℕ) (θ : ℝ) (y : Fin R → ℕ)
    (h : R < 2 * (Finset.univ.filter fun j ↦ IsPhaseEstimate (m + 3) θ (y j : ℤ)).card) :
    IsPhaseEstimate m θ (voteVal (2 ^ (m + 3)) y : ℤ) := by
  classical
  set G := Finset.univ.filter fun j ↦ IsPhaseEstimate (m + 3) θ (y j : ℤ) with hG
  have hnear : ∀ i ∈ G, ∀ j ∈ G, Near (2 ^ (m + 3)) (y j : ℤ) (y i : ℤ) := by
    intro i hi j hj
    simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact near_of_good m θ _ _ hj hi
  obtain ⟨i1, hi1⟩ : G.Nonempty := Finset.card_pos.1 (by omega)
  have hex : ∃ i, R < 2 * cnt (2 ^ (m + 3)) y i := by
    refine ⟨i1, ?_⟩
    have hsub : G ⊆ Finset.univ.filter fun j ↦ Near (2 ^ (m + 3)) (y j : ℤ) (y i1 : ℤ) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hnear i1 hi1 j hj
    have := Finset.card_le_card hsub
    unfold cnt
    omega
  unfold voteVal
  rw [dif_pos hex]
  set i0 := leastIdx hex with hi0def
  have hi0 : R < 2 * cnt (2 ^ (m + 3)) y i0 := leastIdx_spec hex
  set A := Finset.univ.filter fun j ↦ Near (2 ^ (m + 3)) (y j : ℤ) (y i0 : ℤ) with hA
  have hAcard : A.card = cnt (2 ^ (m + 3)) y i0 := rfl
  have hinter : (G ∩ A).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have h1 := Finset.card_union_add_card_inter G A
    rw [hne, Finset.card_empty] at h1
    have h2 : (G ∪ A).card ≤ R := by
      calc (G ∪ A).card ≤ (Finset.univ : Finset (Fin R)).card := Finset.card_le_univ _
        _ = R := by simp
    omega
  obtain ⟨j, hj⟩ := hinter
  rw [Finset.mem_inter] at hj
  have hjG := hj.1
  have hjA := hj.2
  simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hjG
  simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hjA
  obtain ⟨a, ha⟩ := hjG
  obtain ⟨c, hc⟩ := hjA
  refine ⟨a + c, ?_⟩
  set P : ℝ := 2 ^ m with hP
  have hPpos : 0 < P := by positivity
  have hN : (2 : ℝ) ^ (m + 3) = 8 * P := by rw [pow_add]; norm_num [hP]; ring
  rw [hN] at ha
  have hc' : |((y j : ℤ) : ℝ) - (y i0 : ℝ) - (c : ℝ) * (8 * P)| ≤ 2 := by
    have := (Int.cast_le (R := ℝ)).2 hc
    push_cast at this
    rw [hN] at this
    simpa [hN] using this
  set v := (y i0 + 4) / 8 with hv
  have hv1 : 8 * v ≤ y i0 + 4 := Nat.mul_div_le _ _
  have hv2 : y i0 + 4 < 8 * v + 8 := by omega
  have hv1' : (8 : ℝ) * v ≤ y i0 + 4 := by exact_mod_cast hv1
  have hv2' : (y i0 : ℝ) + 4 < 8 * v + 8 := by exact_mod_cast hv2
  have hb : |(y i0 : ℝ) - 8 * v| ≤ 4 := by
    rw [abs_le]; constructor <;> linarith
  have e : θ - (v : ℝ) / P - (((a + c : ℤ)) : ℝ) =
      (θ - (y j : ℝ) / (8 * P) - a) + (((y j : ℤ) : ℝ) - (y i0 : ℝ) - (c : ℝ) * (8 * P)) / (8 * P)
        + ((y i0 : ℝ) - 8 * v) / (8 * P) := by
    push_cast
    field_simp
    ring
  have h8 : (0 : ℝ) < 8 * P := by positivity
  have t1 : |θ - (y j : ℝ) / (8 * P) - a| ≤ 1 / (8 * P) := by simpa using ha
  have t2 : |(((y j : ℤ) : ℝ) - (y i0 : ℝ) - (c : ℝ) * (8 * P)) / (8 * P)| ≤ 2 / (8 * P) := by
    rw [abs_div, abs_of_pos h8]
    exact div_le_div_of_nonneg_right hc' h8.le
  have t3 : |((y i0 : ℝ) - 8 * v) / (8 * P)| ≤ 4 / (8 * P) := by
    rw [abs_div, abs_of_pos h8]
    exact div_le_div_of_nonneg_right hb h8.le
  rw [Int.cast_natCast, e]
  calc _ ≤ |θ - (y j : ℝ) / (8 * P) - a| +
        |(((y j : ℤ) : ℝ) - (y i0 : ℝ) - (c : ℝ) * (8 * P)) / (8 * P)| +
        |((y i0 : ℝ) - 8 * v) / (8 * P)| := abs_add_three _ _ _
    _ ≤ 1 / (8 * P) + 2 / (8 * P) + 4 / (8 * P) := by gcongr
    _ ≤ 1 / P := by
      rw [← add_div, ← add_div, div_le_div_iff₀ h8 hPpos]
      nlinarith

/-! ## Tail bound -/

theorem prod_sum_weight {M : ℕ} (R : ℕ) (p w : Fin M → ℝ) :
    ∑ y : Fin R → Fin M, ∏ i, (p (y i) * w (y i)) = (∑ x, p x * w x) ^ R := by
  have h := Finset.prod_univ_sum (fun _ : Fin R ↦ (Finset.univ : Finset (Fin M)))
    (fun _ x ↦ p x * w x)
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  simp

theorem total_prob {M : ℕ} (R : ℕ) (p : Fin M → ℝ) (hsum : ∑ x, p x = 1) :
    ∑ y : Fin R → Fin M, ∏ i, p (y i) = 1 := by
  have h := prod_sum_weight R p (fun _ ↦ 1)
  simp only [mul_one, hsum, one_pow] at h
  exact h

theorem tail_bound {M : ℕ} (p : Fin M → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (good : Fin M → Prop) [DecidablePred good]
    (hbad : ∑ x, (if good x then 0 else p x) ≤ 1 / 4) (R s : ℕ) (hR : R = 2 * s) :
    ∑ y : Fin R → Fin M, (∏ i, p (y i)) *
      (if 2 * (Finset.univ.filter fun i ↦ good (y i)).card ≤ R then 1 else 0) ≤ (3 / 4) ^ s := by
  set w : Fin M → ℝ := fun x ↦ if good x then 1 else 3 with hw
  have h3 : (0 : ℝ) < 3 ^ s := by positivity
  -- pointwise bound
  have hpt : ∀ y : Fin R → Fin M, (∏ i, p (y i)) *
      (if 2 * (Finset.univ.filter fun i ↦ good (y i)).card ≤ R then 1 else 0) ≤
      (∏ i, (p (y i) * w (y i))) / 3 ^ s := by
    intro y
    have hprod : ∏ i, w (y i) = 3 ^ (Finset.univ.filter fun i ↦ ¬ good (y i)).card := by
      simp only [hw]
      rw [Finset.prod_ite]
      simp
    have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin R)))
      (fun i ↦ good (y i))
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    have hP0 : 0 ≤ ∏ i, p (y i) := Finset.prod_nonneg fun i _ ↦ hp _
    rw [Finset.prod_mul_distrib, hprod]
    split_ifs with hif
    · rw [mul_one, le_div_iff₀ h3]
      have : 3 ^ s ≤ (3 : ℝ) ^ (Finset.univ.filter fun i ↦ ¬ good (y i)).card :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
    · rw [mul_zero]
      positivity
  calc _ ≤ ∑ y : Fin R → Fin M, (∏ i, (p (y i) * w (y i))) / 3 ^ s :=
        Finset.sum_le_sum fun y _ ↦ hpt y
    _ = (∑ x, p x * w x) ^ R / 3 ^ s := by
        rw [← Finset.sum_div, prod_sum_weight]
    _ ≤ (3 / 2) ^ R / 3 ^ s := by
      gcongr
      · exact Finset.sum_nonneg fun x _ ↦ mul_nonneg (hp x) (by simp only [hw]; split_ifs <;> norm_num)
      · have e : ∑ x, p x * w x = 1 + 2 * ∑ x, (if good x then 0 else p x) := by
          have : ∀ x, p x * w x = p x + 2 * (if good x then 0 else p x) := by
            intro x; simp only [hw]; split_ifs <;> ring
          simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
        rw [e]; linarith
    _ = (3 / 4) ^ s := by
        rw [hR, pow_mul, ← div_pow]
        congr 1
        norm_num

open scoped Classical in
theorem success_bound (m k : ℕ) (θ : ℝ) (p : Fin (2 ^ (m + 3)) → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hsum : ∑ x, p x = 1)
    (hgood : 3 / 4 ≤ ∑ x, (if IsPhaseEstimate (m + 3) θ (x.val : ℤ) then p x else 0)) :
    1 - 1 / (2 : ℝ) ^ k ≤ ∑ y : Fin (6 * (k + 1)) → Fin (2 ^ (m + 3)), (∏ i, p (y i)) *
      (if IsPhaseEstimate m θ (voteVal (2 ^ (m + 3)) (fun i ↦ (y i).val) : ℤ) then 1 else 0) := by
  classical
  have hbad : ∑ x, (if IsPhaseEstimate (m + 3) θ (x.val : ℤ) then 0 else p x) ≤ 1 / 4 := by
    have : ∀ x : Fin (2 ^ (m + 3)), (if IsPhaseEstimate (m + 3) θ (x.val : ℤ) then 0 else p x) =
        p x - (if IsPhaseEstimate (m + 3) θ (x.val : ℤ) then p x else 0) := by
      intro x; split_ifs <;> ring
    simp only [this, Finset.sum_sub_distrib, hsum]
    linarith
  have ht := tail_bound p hp hsum (fun x ↦ IsPhaseEstimate (m + 3) θ (x.val : ℤ)) hbad
    (6 * (k + 1)) (3 * (k + 1)) (by ring)
  have htot := total_prob (6 * (k + 1)) p hsum
  have hs : (3 / 4 : ℝ) ^ (3 * (k + 1)) ≤ 1 / 2 ^ k := by
    have h1 : (3 / 4 : ℝ) ^ (3 * (k + 1)) = (27 / 64) ^ (k + 1) := by
      rw [pow_mul]; norm_num
    rw [h1, one_div, ← inv_pow]
    calc (27 / 64 : ℝ) ^ (k + 1) ≤ (2⁻¹) ^ (k + 1) := by gcongr; norm_num
      _ ≤ (2⁻¹) ^ k := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hpt : ∀ y : Fin (6 * (k + 1)) → Fin (2 ^ (m + 3)), (∏ i, p (y i)) -
      (∏ i, p (y i)) * (if 2 * (Finset.univ.filter fun i ↦
        IsPhaseEstimate (m + 3) θ ((y i).val : ℤ)).card ≤ 6 * (k + 1) then 1 else 0) ≤
      (∏ i, p (y i)) *
      (if IsPhaseEstimate m θ (voteVal (2 ^ (m + 3)) (fun i ↦ (y i).val) : ℤ) then 1 else 0) := by
    intro y
    have hP0 : 0 ≤ ∏ i, p (y i) := Finset.prod_nonneg fun i _ ↦ hp _
    by_cases hif : 2 * (Finset.univ.filter fun i ↦
        IsPhaseEstimate (m + 3) θ ((y i).val : ℤ)).card ≤ 6 * (k + 1)
    · rw [if_pos hif]; simp only [mul_one, sub_self]; positivity
    · rw [if_neg hif, mul_zero, sub_zero]
      have := vote_isPE m (6 * (k + 1)) θ (fun i ↦ (y i).val) (by omega)
      rw [if_pos this, mul_one]
  have hsum2 := Finset.sum_le_sum fun y (_ : y ∈ (Finset.univ : Finset (Fin (6 * (k + 1)) → Fin (2 ^ (m + 3))))) ↦ hpt y
  rw [Finset.sum_sub_distrib, htot] at hsum2
  linarith

/-! ## Tensor products on function spaces -/

/-- Kronecker product of a family of matrices. -/
def kron {ι X : Type*} [Fintype ι] (A : ι → Matrix X X ℂ) : Matrix (ι → X) (ι → X) ℂ :=
  Matrix.of fun y x ↦ ∏ i, A i (y i) (x i)

section
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]

lemma kron_mul (A B : ι → Matrix X X ℂ) :
    kron A * kron B = kron (fun i ↦ A i * B i) := by
  ext y z
  simp only [kron, Matrix.mul_apply, Matrix.of_apply]
  have h := Finset.prod_univ_sum (fun i : ι ↦ (Finset.univ : Finset X))
    (fun i x ↦ A i (y i) x * B i x (z i))
  rw [Fintype.piFinset_univ] at h
  rw [h]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  exact (Finset.prod_mul_distrib).symm

lemma kron_one : kron (fun _ : ι ↦ (1 : Matrix X X ℂ)) = 1 := by
  ext y x
  simp only [kron, Matrix.of_apply, Matrix.one_apply]
  by_cases h : y = x
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma kron_star (A : ι → Matrix X X ℂ) : star (kron A) = kron (fun i ↦ star (A i)) := by
  ext y x
  simp [kron, Matrix.star_apply, star_prod]

lemma kron_unitary (A : ι → Matrix X X ℂ) (h : ∀ i, star (A i) * A i = 1) :
    star (kron A) * kron A = 1 := by
  rw [kron_star, kron_mul]
  simp only [h]
  exact kron_one

lemma kron_mulVec_prod (A : ι → Matrix X X ℂ) (φ : ι → X → ℂ) :
    kron A *ᵥ (fun x ↦ ∏ i, φ i (x i)) = fun y ↦ ∏ i, (A i *ᵥ φ i) (y i) := by
  ext y
  simp only [Matrix.mulVec, dotProduct, kron, Matrix.of_apply]
  have h := Finset.prod_univ_sum (fun i : ι ↦ (Finset.univ : Finset X))
    (fun i x ↦ A i (y i) x * φ i x)
  rw [Fintype.piFinset_univ] at h
  rw [h]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  exact (Finset.prod_mul_distrib).symm

lemma single_zero_prod (z : X) :
    (Pi.single (fun _ : ι ↦ z) (1 : ℂ) : (ι → X) → ℂ) =
      fun f ↦ ∏ i, (Pi.single z (1 : ℂ) : X → ℂ) (f i) := by
  ext f
  by_cases h : f = fun _ ↦ z
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Pi.single_eq_of_ne hi _)).symm

end

/-! ## Permutation matrices -/

def permMat {X : Type*} [Fintype X] [DecidableEq X] (σ : Equiv.Perm X) : Matrix X X ℂ :=
  Matrix.of fun a b ↦ if a = σ b then 1 else 0

section
variable {X : Type*} [Fintype X] [DecidableEq X]

lemma permMat_mulVec (σ : Equiv.Perm X) (x : X → ℂ) :
    permMat σ *ᵥ x = fun a ↦ x (σ.symm a) := by
  ext a
  simp only [Matrix.mulVec, dotProduct, permMat, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ.symm a)]
  · simp
  · intro b _ hb
    have : a ≠ σ b := fun h ↦ hb (by rw [h, Equiv.symm_apply_apply])
    simp [this]
  · simp

lemma permMat_unitary (σ : Equiv.Perm X) : star (permMat σ) * permMat σ = 1 := by
  ext a c
  simp only [Matrix.mul_apply, Matrix.star_apply, permMat, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (σ a)]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

end

/-! ## Lifting along an equivalence -/

def liftMat {X Y : Type*} (e : X ≃ Y) (M : Matrix X X ℂ) : Matrix Y Y ℂ :=
  M.submatrix e.symm e.symm

section
variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

lemma liftMat_mul (e : X ≃ Y) (M N : Matrix X X ℂ) :
    liftMat e (M * N) = liftMat e M * liftMat e N := by
  unfold liftMat
  rw [Matrix.submatrix_mul_equiv]

lemma liftMat_star_mul (e : X ≃ Y) (M : Matrix X X ℂ) (h : star M * M = 1) :
    star (liftMat e M) * liftMat e M = 1 := by
  unfold liftMat
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    ← Matrix.star_eq_conjTranspose, h, Matrix.submatrix_one_equiv]

lemma liftMat_diagonal (e : X ≃ Y) (d : X → ℂ) :
    liftMat e (Matrix.diagonal d) = Matrix.diagonal (fun g ↦ d (e.symm g)) := by
  unfold liftMat
  rw [Matrix.submatrix_diagonal_equiv]
  rfl

lemma liftMat_mulVec (e : X ≃ Y) (M : Matrix X X ℂ) (x : Y → ℂ) (g : Y) :
    (liftMat e M *ᵥ x) g = (M *ᵥ (fun f ↦ x (e f))) (e.symm g) := by
  simp only [liftMat, Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  exact Fintype.sum_equiv e.symm _ _ (fun h ↦ by simp)

end
lemma voteVal_lt {R : ℕ} (m : ℕ) (y : Fin R → ℕ) (hy : ∀ i, y i < 2 ^ (m + 3)) :
    voteVal (2 ^ (m + 3)) y < 2 ^ (m + 3) := by
  have h8 : 8 ≤ 2 ^ (m + 3) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (m + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold voteVal
  split_ifs with h
  · have := hy (leastIdx h)
    generalize 2 ^ (m + 3) = M at *
    omega
  · omega
/-- The vote as an element of the output register. -/
noncomputable def voteF (m k : ℕ) (y : Fin (6 * (k + 1)) → Fin (2 ^ (m + 3))) :
    Fin (2 ^ (m + 3)) :=
  ⟨voteVal (2 ^ (m + 3)) (fun i ↦ (y i).val), voteVal_lt m _ fun i ↦ (y i).isLt⟩

/-- Add the vote of the run digits into the output digit (digit `0`). -/
noncomputable def shearEquiv (m k : ℕ) :
    Equiv.Perm (Fin (6 * (k + 1) + 1) → Fin (2 ^ (m + 3))) where
  toFun f := Function.update f 0 (f 0 + voteF m k (fun i ↦ f i.succ))
  invFun f := Function.update f 0 (f 0 - voteF m k (fun i ↦ f i.succ))
  left_inv f := by
    have hv : (fun i : Fin (6 * (k + 1)) ↦
        (Function.update f 0 (f 0 + voteF m k (fun i ↦ f i.succ))) i.succ) =
        fun i ↦ f i.succ := by
      funext i
      exact Function.update_of_ne (Fin.succ_ne_zero i) _ _
    simp [hv]
  right_inv f := by
    have hv : (fun i : Fin (6 * (k + 1)) ↦
        (Function.update f 0 (f 0 - voteF m k (fun i ↦ f i.succ))) i.succ) =
        fun i ↦ f i.succ := by
      funext i
      exact Function.update_of_ne (Fin.succ_ne_zero i) _ _
    simp [hv]

lemma shearEquiv_symm_apply (m k : ℕ) (f : Fin (6 * (k + 1) + 1) → Fin (2 ^ (m + 3))) :
    (shearEquiv m k).symm f =
      Function.update f 0 (f 0 - voteF m k (fun i ↦ f i.succ)) := rfl

/-! ## The index equivalence -/

def baselineQubits (m k : ℕ) : ℕ := (m + 3) * (6 * (k + 1) + 1)

lemma card_eq (m k : ℕ) : (2 ^ (m + 3)) ^ (6 * (k + 1) + 1) = 2 ^ baselineQubits m k :=
  (pow_mul 2 (m + 3) (6 * (k + 1) + 1)).symm

noncomputable def eqv (m k : ℕ) :
    (Fin (6 * (k + 1) + 1) → Fin (2 ^ (m + 3))) ≃ Fin (2 ^ baselineQubits m k) :=
  finFunctionFinEquiv.trans (finCongr (card_eq m k))

lemma eqv_symm_val (m k : ℕ) (g : Fin (2 ^ baselineQubits m k)) (i : Fin (6 * (k + 1) + 1)) :
    ((eqv m k).symm g i).val = g.val / (2 ^ (m + 3)) ^ i.val % 2 ^ (m + 3) := by
  show (finFunctionFinEquiv.symm ((finCongr (card_eq m k)).symm g) i).val = _
  rfl

lemma eqv_symm_zero (m k : ℕ) : (eqv m k).symm 0 = fun _ ↦ 0 := by
  funext i
  apply Fin.ext
  rw [eqv_symm_val]
  simp

/-! ## Kronecker products of diagonals -/

lemma kron_diagonal {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]
    (d : ι → X → ℂ) :
    kron (fun i ↦ Matrix.diagonal (d i)) = Matrix.diagonal (fun f ↦ ∏ i, d i (f i)) := by
  ext y x
  simp only [kron, Matrix.of_apply, Matrix.diagonal_apply]
  by_cases h : y = x
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma mulVec_single_apply {X : Type*} [Fintype X] [DecidableEq X] (M : Matrix X X ℂ) (z f : X) :
    (M *ᵥ Pi.single z (1 : ℂ)) f = M f z := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

lemma blockMat_total (θ : ℝ) (m : ℕ) :
    blockMat θ (oracleCalls m) = Matrix.diagonal (fun g : Fin (2 ^ m) ↦ phaseZ θ ^ g.val) := by
  unfold blockMat
  congr 1
  funext g
  rw [sum_oracleCalls]

/-! ## The circuit -/

/-- The cost constant of the baseline. -/
def baselineRelCost : ℚ≥0 := 48

/-- Wire `j` of run register `i`; digit `0` of the index is the output register. -/
def runWire (m k : ℕ) (i : Fin (6 * (k + 1))) (j : Fin (m + 3)) : Fin (baselineQubits m k) :=
  ⟨(m + 3) * (i.val + 1) + j.val, by
    have hi := i.isLt
    have hj := j.isLt
    unfold baselineQubits
    nlinarith⟩

/-- The oracle calls: every run register gets the calls of textbook phase estimation. -/
def callList (m k : ℕ) : List (Fin (baselineQubits m k)) :=
  (List.finRange (6 * (k + 1))).flatMap fun i ↦ (oracleCalls (m + 3)).map (runWire m k i)

lemma outReg_le (m k : ℕ) : 0 + (m + 3) ≤ baselineQubits m k := by
  unfold baselineQubits
  have : m + 3 ≤ (m + 3) * (6 * (k + 1) + 1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- The output register: the lowest `m + 3` wires. -/
def outReg (m k : ℕ) : QRegister (m + 3) (baselineQubits m k) :=
  QRegister.block 0 (m + 3) (outReg_le m k)

noncomputable def kronA (m k : ℕ) (i : Fin (6 * (k + 1) + 1)) :
    Matrix (Fin (2 ^ (m + 3))) (Fin (2 ^ (m + 3))) ℂ :=
  if i = 0 then 1 else (qftU (m + 3)).1

noncomputable def kronB (m k : ℕ) (i : Fin (6 * (k + 1) + 1)) :
    Matrix (Fin (2 ^ (m + 3))) (Fin (2 ^ (m + 3))) ℂ :=
  if i = 0 then 1 else (iqftU (m + 3)).1

noncomputable def matB (m k : ℕ) :
    Matrix (Fin (6 * (k + 1) + 1) → Fin (2 ^ (m + 3)))
      (Fin (6 * (k + 1) + 1) → Fin (2 ^ (m + 3))) ℂ :=
  permMat (shearEquiv m k) * kron (kronB m k)

lemma kronA_unit (m k : ℕ) (i : Fin (6 * (k + 1) + 1)) :
    star (kronA m k i) * kronA m k i = 1 := by
  unfold kronA
  split_ifs
  · simp
  · exact Matrix.mem_unitaryGroup_iff'.1 (qftU (m + 3)).2

lemma kronB_unit (m k : ℕ) (i : Fin (6 * (k + 1) + 1)) :
    star (kronB m k i) * kronB m k i = 1 := by
  unfold kronB
  split_ifs
  · simp
  · exact Matrix.mem_unitaryGroup_iff'.1 (iqftU (m + 3)).2

lemma matB_unit (m k : ℕ) : star (matB m k) * matB m k = 1 := by
  have hP := permMat_unitary (shearEquiv m k)
  have hK := kron_unitary (kronB m k) (kronB_unit m k)
  unfold matB
  calc star (permMat (shearEquiv m k) * kron (kronB m k)) *
        (permMat (shearEquiv m k) * kron (kronB m k))
      = star (kron (kronB m k)) * (star (permMat (shearEquiv m k)) * permMat (shearEquiv m k)) *
        kron (kronB m k) := by
        rw [star_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hP, Matrix.mul_one, hK]

/-- First fused step: Fourier transform on every run register. -/
noncomputable def stepA (m k : ℕ) : Unitary (2 ^ baselineQubits m k) :=
  ⟨liftMat (eqv m k) (kron (kronA m k)),
    Matrix.mem_unitaryGroup_iff'.2 (liftMat_star_mul _ _ (kron_unitary _ (kronA_unit m k)))⟩

/-- Second fused step: inverse Fourier transform on every run register, then add the vote of the
run values into the output register. -/
noncomputable def stepB (m k : ℕ) : Unitary (2 ^ baselineQubits m k) :=
  ⟨liftMat (eqv m k) (matB m k),
    Matrix.mem_unitaryGroup_iff'.2 (liftMat_star_mul _ _ (matB_unit m k))⟩

/-- The circuit of the baseline. -/
noncomputable def baselineCircuit (m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ baselineQubits m k)) Var (baselineQubits m k) 1 :=
  .seq (.step (stepA m k))
    (.seq (oracleBlock (callList m k))
      (.seq (.step (stepB m k)) (.measure res (outReg m k))))

lemma compile_eq (θ : ℝ) (m k : ℕ) :
    (baselineCircuit m k).compile QProg.qAssign (phaseOracle θ) =
      QProg.qSeq (QProg.qAssign (stepA m k)) (QProg.qSeq (blockProg θ (callList m k))
        (QProg.qSeq (QProg.qAssign (stepB m k))
          (QProg.measureRegister res (outReg m k)))) := by
  simp only [baselineCircuit, OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_step,
    OracleDynamicCircuit.compile_measure, compile_block]

/-! ## Cost -/

lemma unitaryCost_le_one (θ : ℝ) {n : ℕ} (U : Unitary (2 ^ n)) :
    (CostModel.ofEmbeddedOracle (n := n) (phaseOracle θ)).unitaryCost U ≤ 1 := by
  unfold CostModel.ofEmbeddedOracle
  dsimp only
  split_ifs <;> simp

lemma length_flatMap_const {α β : Type*} (l : List α) (F : α → List β) (c : ℕ)
    (h : ∀ a, (F a).length = c) : (l.flatMap F).length = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, List.length_append, h, ih, List.length_cons]; ring

lemma callList_length (m k : ℕ) :
    (callList m k).length + 6 * (k + 1) = 6 * (k + 1) * 2 ^ (m + 3) := by
  unfold callList
  rw [length_flatMap_const _ _ (oracleCalls (m + 3)).length (fun a ↦ by simp), List.length_finRange]
  have := oracleCalls_length (m + 3)
  nlinarith

lemma baseline_cost (θ : ℝ) (m k : ℕ) :
    CostBound (CostModel.ofEmbeddedOracle (phaseOracle θ))
      (QProg.qSeq QProg.qSet ((baselineCircuit m k).compile QProg.qAssign (phaseOracle θ)))
      ((baselineRelCost : ℝ≥0) * 2 ^ m * (k + 1)) := by
  rw [compile_eq]
  refine CostBound.mono (CostBound.seq (CostBound.qSet _) (CostBound.seq (CostBound.qAssign _ _)
    (CostBound.seq (block_cost θ _) (CostBound.seq (CostBound.qAssign _ _)
    (CostBound.qMeasure _ _ _))))) ?_
  have hA := unitaryCost_le_one θ (stepA m k)
  have hB := unitaryCost_le_one θ (stepB m k)
  have h48 : ((baselineRelCost : ℚ≥0) : ℝ≥0) = 48 := by
    unfold baselineRelCost; norm_num
  have hnat : 2 + (callList m k).length ≤ 48 * 2 ^ m * (k + 1) := by
    have h := callList_length m k
    have h8 : 2 ^ (m + 3) = 8 * 2 ^ m := by rw [pow_add]; ring
    rw [h8] at h
    nlinarith
  have hcast : (2 : ℝ≥0) + ((callList m k).length : ℝ≥0) ≤ 48 * 2 ^ m * (k + 1) := by
    exact_mod_cast hnat
  rw [h48]
  refine le_trans ?_ hcast
  have hA' : ((CostModel.ofEmbeddedOracle (n := baselineQubits m k) (phaseOracle θ)).unitaryCost
      (stepA m k) : ℝ≥0) ≤ 1 := by exact_mod_cast hA
  have hB' : ((CostModel.ofEmbeddedOracle (n := baselineQubits m k) (phaseOracle θ)).unitaryCost
      (stepB m k) : ℝ≥0) ≤ 1 := by exact_mod_cast hB
  have key : ∀ r a b l c : ℝ≥0, a ≤ 1 → b ≤ 1 → r = 0 → c = 0 →
      r + (a + (l + (b + c))) ≤ 2 + l := by
    intro r a b l c ha hb hr hc
    subst hr hc
    calc 0 + (a + (l + (b + 0))) = (a + b) + l := by ring
      _ ≤ 2 + l := by
        have : a + b ≤ 2 := by
          calc a + b ≤ 1 + 1 := add_le_add ha hb
            _ = 2 := one_add_one_eq_two
        gcongr
  exact key _ _ _ _ _ hA' hB' (by simp [CostModel.ofEmbeddedOracle])
    (by simp [CostModel.ofEmbeddedOracle])

/-! ## Bits of the run registers -/

lemma bit_mod (M j x : ℕ) (hj : j < M) : x % 2 ^ M / 2 ^ j % 2 = x / 2 ^ j % 2 := by
  obtain ⟨d, rfl⟩ : ∃ d, M = j + 1 + d := ⟨M - j - 1, by omega⟩
  have h1 : 2 ^ (j + 1 + d) = 2 ^ j * 2 ^ (d + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [h1, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))

lemma extract_block_val {n : ℕ} (w : ℕ) (h : 0 + w ≤ n) (g : Fin (2 ^ n)) :
    (((QRegister.block 0 w h).extractIndex g : Fin (2 ^ w)) : ℕ) = g.val % 2 ^ w := by
  have hlt : g.val % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
  have key : (QRegister.block 0 w h).extractIndex g = ⟨g.val % 2 ^ w, hlt⟩ := by
    apply (basisBits w).injective
    funext i
    rw [QRegister.basisBits_extractIndex, basisBits_eq_div_mod, basisBits_eq_div_mod]
    congr 1
    show g.val / 2 ^ (0 + i.val) % 2 = g.val % 2 ^ w / 2 ^ i.val % 2
    rw [bit_mod w i.val g.val i.isLt, zero_add]
  rw [key]

lemma extract_outReg (m k : ℕ) (g : Fin (2 ^ baselineQubits m k)) :
    (((outReg m k).extractIndex g : Fin (2 ^ (m + 3))) : ℕ) = g.val % 2 ^ (m + 3) :=
  extract_block_val (m + 3) (outReg_le m k) g

lemma bitN_runWire (m k : ℕ) (i : Fin (6 * (k + 1))) (j : Fin (m + 3))
    (g : Fin (2 ^ baselineQubits m k)) :
    bitN (runWire m k i j) g =
      bitN j (⟨g.val / (2 ^ (m + 3)) ^ (i.val + 1) % 2 ^ (m + 3),
        Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : Fin (2 ^ (m + 3))) := by
  unfold bitN
  show g.val / 2 ^ ((m + 3) * (i.val + 1) + j.val) % 2 =
    g.val / (2 ^ (m + 3)) ^ (i.val + 1) % 2 ^ (m + 3) / 2 ^ j.val % 2
  have e : 2 ^ ((m + 3) * (i.val + 1) + j.val) = (2 ^ (m + 3)) ^ (i.val + 1) * 2 ^ j.val := by
    rw [Nat.pow_add 2 ((m + 3) * (i.val + 1)) j.val, pow_mul]
  rw [e, bit_mod (m + 3) j.val _ j.isLt, Nat.div_div_eq_div_mul]

lemma sum_flatMap_map {α β : Type*} (l : List α) (F : α → List β) (h : β → ℕ) :
    ((l.flatMap F).map h).sum = (l.map fun a ↦ ((F a).map h).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

lemma callList_sum (m k : ℕ) (g : Fin (2 ^ baselineQubits m k)) :
    ((callList m k).map fun j ↦ bitN j g).sum =
      ∑ i : Fin (6 * (k + 1)), (((eqv m k).symm g) i.succ).val := by
  unfold callList
  rw [sum_flatMap_map, ← Fin.sum_univ_def]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [List.map_map]
  have h : ((fun j ↦ bitN j g) ∘ runWire m k i) = fun j' ↦ bitN j'
      (⟨g.val / (2 ^ (m + 3)) ^ (i.val + 1) % 2 ^ (m + 3),
        Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : Fin (2 ^ (m + 3))) :=
    funext fun j ↦ bitN_runWire m k i j g
  rw [h, sum_oracleCalls, eqv_symm_val, Fin.val_succ]

lemma blockMat_call (θ : ℝ) (m k : ℕ) :
    blockMat θ (callList m k) = liftMat (eqv m k) (kron fun i : Fin (6 * (k + 1) + 1) ↦
      Matrix.diagonal (fun x : Fin (2 ^ (m + 3)) ↦ if i = 0 then (1 : ℂ) else phaseZ θ ^ x.val)) := by
  rw [kron_diagonal, liftMat_diagonal]
  unfold blockMat
  congr 1
  funext g
  rw [callList_sum, ← Finset.prod_pow_eq_pow_sum, Fin.prod_univ_succ (n := 6 * (k + 1))]
  simp

/-! ## The whole matrix -/

/-- The matrix of the three steps, before relabelling the index. -/
noncomputable def Phi (θ : ℝ) (m k : ℕ) :
    Matrix (Fin (6 * (k + 1) + 1) → Fin (2 ^ (m + 3)))
      (Fin (6 * (k + 1) + 1) → Fin (2 ^ (m + 3))) ℂ :=
  permMat (shearEquiv m k) * kron (fun i : Fin (6 * (k + 1) + 1) ↦
    if i = 0 then (1 : Matrix (Fin (2 ^ (m + 3))) (Fin (2 ^ (m + 3))) ℂ) else Wm (m + 3) θ)

lemma digit_eq (θ : ℝ) (m k : ℕ) (i : Fin (6 * (k + 1) + 1)) :
    kronB m k i * Matrix.diagonal (fun x : Fin (2 ^ (m + 3)) ↦
      if i = 0 then (1 : ℂ) else phaseZ θ ^ x.val) * kronA m k i =
    if i = 0 then (1 : Matrix (Fin (2 ^ (m + 3))) (Fin (2 ^ (m + 3))) ℂ) else Wm (m + 3) θ := by
  unfold kronA kronB
  by_cases h : i = 0
  · simp [h]
  · simp only [if_neg h]
    unfold Wm
    rw [iqftU_val, qftU_val]

lemma total_eq (θ : ℝ) (m k : ℕ) :
    (stepB m k).1 * blockMat θ (callList m k) * (stepA m k).1 =
      liftMat (eqv m k) (Phi θ m k) := by
  rw [blockMat_call]
  show liftMat (eqv m k) (matB m k) * _ * liftMat (eqv m k) (kron (kronA m k)) = _
  rw [← liftMat_mul, ← liftMat_mul]
  congr 1
  unfold Phi matB
  have h : kron (kronB m k) * kron (fun i : Fin (6 * (k + 1) + 1) ↦
      Matrix.diagonal (fun x : Fin (2 ^ (m + 3)) ↦ if i = 0 then (1 : ℂ) else phaseZ θ ^ x.val)) *
      kron (kronA m k) = kron (fun i : Fin (6 * (k + 1) + 1) ↦
        if i = 0 then (1 : Matrix (Fin (2 ^ (m + 3))) (Fin (2 ^ (m + 3))) ℂ) else Wm (m + 3) θ) := by
    rw [kron_mul, kron_mul]
    congr 1
    funext i
    exact digit_eq θ m k i
  rw [← h]
  simp only [Matrix.mul_assoc]

lemma Phi_apply (θ : ℝ) (m k : ℕ) (f : Fin (6 * (k + 1) + 1) → Fin (2 ^ (m + 3))) :
    Phi θ m k f (fun _ ↦ 0) =
      (if f 0 = voteF m k (fun i ↦ f i.succ) then 1 else 0) *
        ∏ i : Fin (6 * (k + 1)), Wm (m + 3) θ (f i.succ) 0 := by
  rw [← mulVec_single_apply (Phi θ m k) (fun _ ↦ 0) f, single_zero_prod]
  unfold Phi
  rw [← Matrix.mulVec_mulVec, permMat_mulVec, kron_mulVec_prod]
  simp only []
  rw [Fin.prod_univ_succ (n := 6 * (k + 1))]
  simp [shearEquiv_symm_apply, Function.update_of_ne, Fin.succ_ne_zero, mulVec_single_apply,
    Matrix.one_apply, sub_eq_zero, ite_mul, one_mul, zero_mul]

/-! ## Probabilities -/

open scoped Classical in
/-- The success probability of the baseline. -/
noncomputable def probP (m k : ℕ) (θ : ℝ) : ℝ :=
  ∑ y : Fin (6 * (k + 1)) → Fin (2 ^ (m + 3)),
    (∏ i, Complex.normSq (Wm (m + 3) θ (y i) 0)) *
      (if IsPhaseEstimate m θ ((voteF m k y).val : ℤ) then 1 else 0)

open scoped Classical in
noncomputable def gF (θ : ℝ) (m k : ℕ) (f : Fin (6 * (k + 1) + 1) → Fin (2 ^ (m + 3))) : ℝ :=
  if IsPhaseEstimate m θ ((f 0).val : ℤ) then Complex.normSq (Phi θ m k f (fun _ ↦ 0)) else 0

open scoped Classical in
lemma sum_formula (θ : ℝ) (m k : ℕ) :
    (∑ g : Fin (2 ^ baselineQubits m k),
      if IsPhaseEstimate m θ (((outReg m k).extractIndex g).val : ℤ)
      then Complex.normSq ((liftMat (eqv m k) (Phi θ m k)) g 0) else 0) = probP m k θ := by
  have h1 : ∀ g : Fin (2 ^ baselineQubits m k),
      (if IsPhaseEstimate m θ (((outReg m k).extractIndex g).val : ℤ)
        then Complex.normSq ((liftMat (eqv m k) (Phi θ m k)) g 0) else 0) =
      gF θ m k ((eqv m k).symm g) := by
    intro g
    have e0 : (((outReg m k).extractIndex g : Fin (2 ^ (m + 3))) : ℕ) =
        (((eqv m k).symm g) 0).val := by
      rw [extract_outReg, eqv_symm_val]
      simp
    have e1 : (liftMat (eqv m k) (Phi θ m k)) g 0 = Phi θ m k ((eqv m k).symm g) (fun _ ↦ 0) := by
      show Phi θ m k ((eqv m k).symm g) ((eqv m k).symm 0) = _
      rw [eqv_symm_zero]
    rw [e0, e1]
    rfl
  calc _ = ∑ g : Fin (2 ^ baselineQubits m k), gF θ m k ((eqv m k).symm g) :=
        Finset.sum_congr rfl fun g _ ↦ h1 g
    _ = ∑ f, gF θ m k f := Equiv.sum_comp (eqv m k).symm (gF θ m k)
    _ = probP m k θ := by
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (6 * (k + 1) + 1) ↦ Fin (2 ^ (m + 3)))) (gF θ m k),
        Fintype.sum_prod_type, Finset.sum_comm]
      unfold probP
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [Finset.sum_eq_single (voteF m k y)]
      · simp only [gF, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ, Phi_apply]
        by_cases hp : IsPhaseEstimate m θ ((voteF m k y).val : ℤ)
        · simp [hp, map_prod]
        · simp [hp]
      · intro a _ ha
        simp [gF, Fin.consEquiv_apply, Phi_apply, ha]
      · simp

open scoped Classical in
lemma prob_formula (θ : ℝ) (m k : ℕ) :
    ((liftMat (eqv m k) (Phi θ m k))ᴴ * Matrix.diagonal
      (fun g : Fin (2 ^ baselineQubits m k) ↦
        if IsPhaseEstimate m θ (((outReg m k).extractIndex g).val : ℤ) then (1 : ℂ) else 0) *
      liftMat (eqv m k) (Phi θ m k)) 0 0 = ((probP m k θ : ℝ) : ℂ) := by
  rw [entry (baselineQubits m k) (liftMat (eqv m k) (Phi θ m k))
    (fun g ↦ IsPhaseEstimate m θ (((outReg m k).extractIndex g).val : ℤ)), sum_formula]

/-! ## Unitarity and the success bound -/

lemma blockMat_unitary (θ : ℝ) {n : ℕ} (l : List (Fin n)) :
    star (blockMat θ l) * blockMat θ l = 1 := by
  induction l with
  | nil => simp [blockMat]
  | cons j l ih =>
    have hU := Matrix.mem_unitaryGroup_iff'.1 (oraU θ j).2
    rw [blockMat_cons, star_mul]
    calc star (oraU θ j).1 * star (blockMat θ l) * (blockMat θ l * (oraU θ j).1)
        = star (oraU θ j).1 * (star (blockMat θ l) * blockMat θ l) * (oraU θ j).1 := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ih, Matrix.mul_one, hU]

lemma Wm_unitary (m : ℕ) (θ : ℝ) : star (Wm m θ) * Wm m θ = 1 := by
  have hQ := Matrix.mem_unitaryGroup_iff'.1 (qftU m).2
  have hQ' := Matrix.mem_unitaryGroup_iff.1 (qftU m).2
  have hB := blockMat_unitary θ (oracleCalls m)
  have hW : Wm m θ = star (qftU m).1 * blockMat θ (oracleCalls m) * (qftU m).1 := by
    rw [blockMat_total, qftU_val]; rfl
  rw [hW]
  calc star (star (qftU m).1 * blockMat θ (oracleCalls m) * (qftU m).1) *
        (star (qftU m).1 * blockMat θ (oracleCalls m) * (qftU m).1)
      = star (qftU m).1 * (star (blockMat θ (oracleCalls m)) * ((qftU m).1 * star (qftU m).1) *
          blockMat θ (oracleCalls m)) * (qftU m).1 := by
        simp only [star_mul, star_star, Matrix.mul_assoc]
    _ = 1 := by rw [hQ', Matrix.mul_one, hB, Matrix.mul_one, hQ]

open scoped Classical in
lemma sum_p (m : ℕ) (θ : ℝ) : ∑ x : Fin (2 ^ m), Complex.normSq (Wm m θ x 0) = 1 := by
  have h := entry m (Wm m θ) (fun _ ↦ True)
  simp only [if_true, Matrix.diagonal_one, Matrix.mul_one, ← Matrix.star_eq_conjTranspose,
    Wm_unitary] at h
  have h2 : ((∑ x : Fin (2 ^ m), Complex.normSq (Wm m θ x 0) : ℝ) : ℂ) = 1 := by
    rw [← h]; simp
  exact_mod_cast h2

open scoped Classical in
lemma probP_ge (θ : ℝ) (m k : ℕ) : 1 - 1 / (2 : ℝ) ^ k ≤ probP m k θ := by
  refine success_bound m k θ (fun x ↦ Complex.normSq (Wm (m + 3) θ x 0))
    (fun x ↦ Complex.normSq_nonneg _) (sum_p (m + 3) θ) ?_
  have := succ_ge (m + 3) θ
  unfold succM at this
  norm_num at this ⊢
  linarith

/-! ## The triple -/

open scoped Classical in
lemma meas_mat' {n w : ℕ} (r : QRegister w n) (m : ℕ) (θ : ℝ) (σ : Store Var) :
    ((wp (QProg.measureRegister res r : QProg Var (2 ^ n))
      (fun σ ↦ ⌜IsPhaseEstimate m θ (σ res)⌝)) σ).1.mat =
      Matrix.diagonal (fun g : Fin (2 ^ n) ↦
        if IsPhaseEstimate m θ ((r.extractIndex g).val : ℤ) then 1 else 0) := by
  simp only [wp, QProg.measureRegister, CQAssertion.qMeasure_coe]
  change HermitianMat.mat (∑ o : Fin (2 ^ w), (_ : HermitianMat (Fin (2 ^ n)) ℂ)) = _
  rw [HermitianMat.mat_finset_sum]
  ext i j
  simp [HermitianMat.conj_apply_mat, Store.subst, Observable.ofProp, apply_ite,
    QRegister.computationalBasisMeasurement_apply,
    QRegister.basisOutcomeProjector_eq_diagonal, Matrix.sum_apply,
    Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    split_ifs with hp
    · refine (Finset.sum_eq_single (r.extractIndex i) (fun c _ hc ↦ ?_) (by simp)).trans ?_
      · split_ifs <;> simp [Matrix.diagonal_apply, Ne.symm hc]
      · split_ifs <;> first | simp [Matrix.diagonal_apply] | contradiction
    · refine Finset.sum_eq_zero fun c _ ↦ ?_
      split_ifs with hc
      · have hci : c ≠ r.extractIndex i := by rintro rfl; exact hp hc
        simp [Matrix.diagonal_apply, Ne.symm hci]
      · simp
  · rw [if_neg hij]
    refine Finset.sum_eq_zero fun c _ ↦ ?_
    split_ifs <;> simp [Matrix.diagonal_apply_ne _ hij]

lemma total_mat' {d : ℕ} (A B Bl D : Matrix (Fin d) (Fin d) ℂ) :
    Aᴴ * (star Bl * (Bᴴ * D * B) * Bl) * A = (B * Bl * A)ᴴ * D * (B * Bl * A) := by
  simp only [← Matrix.star_eq_conjTranspose, star_mul, star_star, Matrix.mul_assoc]

open scoped Classical in
lemma wp_mat (θ : ℝ) (m k : ℕ) (σ : Store Var) :
    ((wp (qset ;; (baselineCircuit m k).compile QProg.qAssign (phaseOracle θ))
      (fun σ ↦ ⌜IsPhaseEstimate m θ (σ res)⌝)) σ).1.mat =
      ((probP m k θ : ℝ) : ℂ) • (1 : Matrix (Fin (2 ^ baselineQubits m k))
        (Fin (2 ^ baselineQubits m k)) ℂ) := by
  rw [compile_eq]
  simp only [wp_qSeq, wp_qSet, wp_qAssign]
  rw [CQAssertion.qSet_apply_mat, CQAssertion.qAssign_apply_mat, block_wp_mat,
    CQAssertion.qAssign_apply_mat, meas_mat', total_mat', total_eq]
  congr 1
  exact prob_formula θ m k

lemma baseline_triple (θ : ℝ) (m k : ℕ) :
    ⦃ CQAssertion.ofProb (1 - 1 / (2 : ℝ) ^ k) ⦄
      (qset ;; (baselineCircuit m k).compile QProg.qAssign (phaseOracle θ))
      ⦃ fun σ ↦ ⌜IsPhaseEstimate m θ (σ res)⌝ ⦄ := by
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have hdiv : 1 / (2 : ℝ) ^ k ≤ 1 := by rw [div_le_one hpos]; exact h2k
  have hdiv0 : 0 ≤ 1 / (2 : ℝ) ^ k := by positivity
  refine Triple.of_le_wp fun σ ↦ Subtype.coe_le_coe.mp ?_
  rw [CQAssertion.ofProb_apply_of_bounds _ (by linarith) (by linarith)]
  have h : ((wp (qset ;; (baselineCircuit m k).compile QProg.qAssign (phaseOracle θ))
      (fun σ ↦ ⌜IsPhaseEstimate m θ (σ res)⌝)) σ).1 =
      probP m k θ • (1 : HermitianMat (Fin (2 ^ baselineQubits m k)) ℂ) := by
    apply HermitianMat.ext
    rw [wp_mat, HermitianMat.mat_smul, HermitianMat.mat_one, Complex.coe_smul]
  rw [h]
  exact smul_le_smul_of_nonneg_right (probP_ge θ m k) zero_le_one

end PhaseEstBaselineGeneral

/-- Total number of qubits used by `phaseEstCircuit`. -/
def phaseEstQubits (m k : ℕ) : ℕ := PhaseEstBaselineGeneral.baselineQubits m k

/-- Query-model circuit on `phaseEstQubits m k` qubits with single-qubit phase-oracle calls that
writes an `m`-bit estimate of the oracle phase into `res`. -/
noncomputable def phaseEstCircuit (m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ phaseEstQubits m k)) Var (phaseEstQubits m k) 1 :=
  PhaseEstBaselineGeneral.baselineCircuit m k

open QProg.Notation in
/-- Reset all qubits, then run `phaseEstCircuit` compiled with `oracle`. -/
noncomputable def phaseEstProgram (m k : ℕ)
    (oracle : Unitary (2 ^ 1)) : QProg Var (2 ^ phaseEstQubits m k) :=
  qset ;; (phaseEstCircuit m k).compile QProg.qAssign oracle

/-- `phaseEstProgram m k` writes an `m`-bit estimate of `θ` into `res` with probability at least
`1 - 1 / 2 ^ k`, for every precision `m`, confidence parameter `k` and phase `θ`. -/
theorem phaseEst_correctness (m k : ℕ) (θ : ℝ) :
    ⦃ CQAssertion.ofProb (1 - 1 / (2 : ℝ) ^ k) ⦄
    phaseEstProgram m k (phaseOracle θ)
    ⦃ fun σ ↦ ⌜IsPhaseEstimate m θ (σ res)⌝ ⦄ := by
  exact PhaseEstBaselineGeneral.baseline_triple θ m k

/-- Claimed constant in the expected oracle-call bound `phaseEstRelCost * 2 ^ m * (k + 1)`. -/
def phaseEstRelCost : ℚ≥0 := 48

/-- Expected oracle-call bound for `phaseEstProgram m k`, uniform in `m`, `k` and `θ`. -/
theorem phaseEst_rel_cost (m k : ℕ) (θ : ℝ) :
    CostBound (CostModel.ofEmbeddedOracle (phaseOracle θ))
      (phaseEstProgram m k (phaseOracle θ))
      (phaseEstRelCost * 2 ^ m * (k + 1)) := by
  exact PhaseEstBaselineGeneral.baseline_cost θ m k

/-!
## Pinned instance

A single-number record at precision `m = 10` (additive error `1 / 1024`) and confidence `k = 10`
(failure probability at most `1 / 1024`): the expected number of oracle calls of
`phaseEstProgram` at that size is bounded by a closed constant. A solution may treat the pinned
size separately from the general family.
-/

/-- Claimed expected oracle-call bound for `phaseEstProgram` at `m = 10`, `k = 10`. -/
def phaseEstM10K10ConstCost : ℚ≥0 := 540672

/-- Expected oracle-call bound at the pinned size `m = 10`, `k = 10`, uniform in `θ`. -/
theorem phaseEst_m10_k10_const_cost (θ : ℝ) :
    CostBound (CostModel.ofEmbeddedOracle (phaseOracle θ))
      (phaseEstProgram 10 10 (phaseOracle θ))
      phaseEstM10K10ConstCost := by
  refine CostBound.mono (PhaseEstBaselineGeneral.baseline_cost θ 10 10) ?_
  unfold phaseEstM10K10ConstCost PhaseEstBaselineGeneral.baselineRelCost
  norm_num

end QuantumComputation.Specs
