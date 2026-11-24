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
public import Mathlib.LinearAlgebra.Matrix.Block
public import QuantumComputation.QuantumHoareLogic.WP
public import QuantumComputation.Primitives.Phase
public import QuantumComputation.Algorithms.QFT.States
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds


/-!
# Amplitude Estimation Specification

Query-model specification for estimating the success probability
`a = ‖(1 ⊗ ⟨1|) A |0…0⟩‖²` of an unknown `n`-qubit state-preparation unitary `A`, where the flag
is the lowest-order bit of the basis index (logical wire `0` under the little-endian `QRegister`
convention): `a` is the probability that measuring the flag of `A |0…0⟩` gives `1`
(G. Brassard, P. Høyer, M. Mosca, A. Tapp, arXiv:quant-ph/0005055).

The oracle is the `(n + 1)`-qubit select unitary `|0⟩⟨0| ⊗ A + |1⟩⟨1| ⊗ A⁻¹` on the select bit
(logical wire `0` of the oracle register) and the `n` wires of `A` (logical wires `1..n`), so one
oracle call applies `A`, its inverse, or a superposition of both, and each costs `1`. Its entry at
`(2 * x + b, 2 * y + c)` is `A x y` if `b = c = 0`, `A⁻¹ x y` if `b = c = 1`, and `0` otherwise.

For every `n`, precision `m` and confidence parameter `k`, the program is an adaptive dynamic
circuit (mid-circuit measurements, `.qIf`, and `.qWhile` allowed) that starts from all qubits
reset and writes an integer `res` with `|a - res / 2 ^ m| ≤ 1 / 2 ^ m`, with probability at least
`1 - 1 / 2 ^ k`, for every unitary `A` (runs that never terminate count as failures; for `k = 0`
the condition is empty, and `m ≤ 1` needs no oracle call). Qubit count, non-oracle unitaries and
classical conditions are free.

The resource metric is the expected number of oracle calls, evaluated semantically on the compiled
program via `CostModel.ofEmbeddedOracle`, charging `1` per oracle call and `0` for all other
operations (except any unitary step whose matrix happens to coincide with an embedded oracle call;
see `CostModel.ofEmbeddedOracle`). The claimed bound is `ampEstRelCost * 2 ^ m * (k + 1)`,
uniformly in `n`, `m`, `k` and `A`, so a solution competes on the constant `ampEstRelCost` in
front of the quadratically improved scaling `(1 / ε) * log (1 / δ)` at additive error
`ε = 1 / 2 ^ m`.
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator ResourceCounting Real
open scoped NNReal NNRat Matrix

/-- By default we allow only a single variable. -/
inductive AmpEst.Var where | res deriving DecidableEq, Inhabited

open AmpEst (Var)
open AmpEst.Var (res)

/-- Success probability of `A`: the probability that the flag (lowest-order bit of the basis
index) of `A |0…0⟩` is `1`. -/
noncomputable def ampEstAmplitude {n : ℕ} (A : Unitary (2 ^ n)) : ℝ :=
  ∑ x : Fin (2 ^ n), if x.val % 2 = 1 then ‖A.1 x ⟨0, Nat.two_pow_pos n⟩‖ ^ 2 else 0

/-- The two diagonal blocks of the select unitary: `A` for select bit `0`, `A⁻¹` for select
bit `1`. -/
noncomputable def ampEstBlocks {n : ℕ} (A : Unitary (2 ^ n)) (b : Fin 2) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  if b = 0 then A.1 else (A⁻¹).1

/-- Select unitary `|0⟩⟨0| ⊗ A + |1⟩⟨1| ⊗ A⁻¹` indexed by `Fin (2 ^ n * 2)`: under
`finProdFinEquiv : (x, b) ↦ b + 2 * x`, the block `b = 0` is `A` and the block `b = 1` is `A⁻¹`. -/
noncomputable def ampEstSelect {n : ℕ} (A : Unitary (2 ^ n)) : Unitary (2 ^ n * 2) :=
  ⟨Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.blockDiagonal (ampEstBlocks A)), by
    have h : (fun b : Fin 2 ↦ ampEstBlocks A b * (ampEstBlocks A b)ᴴ) = 1 := by
      funext b
      unfold ampEstBlocks
      split_ifs
      · exact Matrix.mem_unitaryGroup_iff.mp A.2
      · exact Matrix.mem_unitaryGroup_iff.mp (A⁻¹).2
    have key : Matrix.blockDiagonal (ampEstBlocks A) * (Matrix.blockDiagonal (ampEstBlocks A))ᴴ
        = 1 := by
      rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul, h,
        Matrix.blockDiagonal_one]
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.reindex_apply,
      Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, key, Matrix.submatrix_one_equiv]⟩

/-- Select oracle `|0⟩⟨0| ⊗ A + |1⟩⟨1| ⊗ A⁻¹` on `n + 1` qubits (`2 ^ (n + 1) = 2 ^ n * 2`
definitionally).

Under the little-endian `QRegister` convention, logical wire `0` is the select bit `b` and logical
wires `1..n` hold the `n`-qubit index `x` of `A`. -/
noncomputable def ampEstOracle {n : ℕ} (A : Unitary (2 ^ n)) : Unitary (2 ^ (n + 1)) :=
  ampEstSelect A

/-! ## Baseline: coherent majority vote (helpers)

Proved in a separate working file (not published here); copied here under a separate namespace, with its
copies of the spec definitions removed so that it uses the ones above. -/

namespace AmpEstBaselineGeneral

set_option autoImplicit true

/-- The integer `y` is an `m`-bit estimate of `θ`: `y / 2 ^ m` is within `1 / 2 ^ m` of `θ`
modulo `1`. -/
def IsPhaseEstimate (m : ℕ) (θ : ℝ) (y : ℤ) : Prop :=
  ∃ j : ℤ, |θ - (y : ℝ) / (2 : ℝ) ^ m - (j : ℝ)| ≤ 1 / (2 : ℝ) ^ m

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


/-- `exp(2πiθ)`. -/
noncomputable def phaseZ (θ : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * (θ : ℂ))

/-- The bit of the basis index `g` on wire `j`. -/
def bitN {m : ℕ} (j : Fin m) (g : Fin (2 ^ m)) : ℕ := g.val / 2 ^ j.val % 2

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

open scoped Kronecker

/-! ## Layout -/

/-- Number of qubits: oracle register (`n + 1`), counting register, output register. -/
abbrev qq (n m : ℕ) : ℕ := (n + 1) + (m + 3) + (m + 3)

/-- Basis states `((o, c), (a, s))`: output, counting, `A`'s register, select bit. -/
abbrev PT (n m : ℕ) :=
  (Fin (2 ^ (m + 3)) × Fin (2 ^ (m + 3))) × (Fin (2 ^ n) × Fin 2)

lemma card_qq (n m : ℕ) : 2 ^ (m + 3) * 2 ^ (m + 3) * (2 ^ n * 2) = 2 ^ qq n m := by
  unfold qq; rw [pow_add, pow_add, pow_succ]; ring

noncomputable def eP (n m : ℕ) : PT n m ≃ Fin (2 ^ qq n m) :=
  (Equiv.prodCongr finProdFinEquiv finProdFinEquiv).trans
    (finProdFinEquiv.trans (finCongr (card_qq n m)))

lemma eP_val (n m : ℕ) (o c : Fin (2 ^ (m + 3))) (a : Fin (2 ^ n)) (s : Fin 2) :
    ((eP n m ((o, c), (a, s))) : ℕ) =
      (s.val + 2 * a.val) + 2 ^ n * 2 * (c.val + 2 ^ (m + 3) * o.val) := by
  simp [eP, finProdFinEquiv]

/-- The oracle register: the low `n + 1` wires. -/
noncomputable def regO (n m : ℕ) : QRegister (n + 1) (qq n m) :=
  QRegister.block 0 (n + 1) (by unfold qq; omega)

/-- The output register: the top `m + 3` wires. -/
noncomputable def regR (n m : ℕ) : QRegister (m + 3) (qq n m) :=
  QRegister.block (n + 1 + (m + 3)) (m + 3) (by unfold qq; omega)

/-! ## Step matrices on `PT` -/

def Xm : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- A matrix on the counting register, identity elsewhere. -/
noncomputable def kF (n m : ℕ) (U : Matrix (Fin (2 ^ (m + 3))) (Fin (2 ^ (m + 3))) ℂ) :
    Matrix (PT n m) (PT n m) ℂ :=
  ((1 : Matrix (Fin (2 ^ (m + 3))) (Fin (2 ^ (m + 3))) ℂ) ⊗ₖ U) ⊗ₖ
    (1 : Matrix (Fin (2 ^ n) × Fin 2) (Fin (2 ^ n) × Fin 2) ℂ)

/-- Flip of the select bit. -/
noncomputable def flipP (n m : ℕ) : Matrix (PT n m) (PT n m) ℂ :=
  (1 : Matrix (Fin (2 ^ (m + 3)) × Fin (2 ^ (m + 3))) (Fin (2 ^ (m + 3)) × Fin (2 ^ (m + 3))) ℂ) ⊗ₖ
    ((1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) ⊗ₖ Xm)

/-- Sign `(-1) ^ (c_j * flag a)`: controlled `S_chi`. -/
noncomputable def phA (n m : ℕ) (j : Fin (m + 3)) : PT n m → ℂ :=
  fun y ↦ if bitN j y.1.2 = 1 ∧ y.2.1.val % 2 = 1 then -1 else 1

/-- Sign `-1` when `c_j = 1` and `a ≠ 0`: controlled `-S_0`. -/
noncomputable def phB (n m : ℕ) (j : Fin (m + 3)) : PT n m → ℂ :=
  fun y ↦ if bitN j y.1.2 = 1 ∧ y.2.1 ≠ 0 then -1 else 1

noncomputable def aM (n m : ℕ) (j : Fin (m + 3)) : Matrix (PT n m) (PT n m) ℂ :=
  flipP n m * Matrix.diagonal (phA n m j)

noncomputable def bM (n m : ℕ) (j : Fin (m + 3)) : Matrix (PT n m) (PT n m) ℂ :=
  flipP n m * Matrix.diagonal (phB n m j)

/-- The oracle on `A`'s register and the select bit, identity on the rest. -/
noncomputable def oraP {n : ℕ} (A : Unitary (2 ^ n)) (m : ℕ) : Matrix (PT n m) (PT n m) ℂ :=
  (1 : Matrix (Fin (2 ^ (m + 3)) × Fin (2 ^ (m + 3))) (Fin (2 ^ (m + 3)) × Fin (2 ^ (m + 3))) ℂ) ⊗ₖ
    (liftMat (finProdFinEquiv.symm : Fin (2 ^ n * 2) ≃ Fin (2 ^ n) × Fin 2) (ampEstOracle A).1)

/-- The rounded value written to the output register. -/
noncomputable def rv (m : ℕ) (c : Fin (2 ^ (m + 3))) : ℕ :=
  ⌊(2 : ℝ) ^ m * Real.sin (π * c.val / 2 ^ (m + 3)) ^ 2 + 1 / 2⌋₊

lemma rv_lt (m : ℕ) (c : Fin (2 ^ (m + 3))) : rv m c < 2 ^ (m + 3) := by
  unfold rv
  have hP : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have h1 := Real.sin_sq_le_one (π * c.val / 2 ^ (m + 3))
  have h2 : (2 : ℝ) ^ m * Real.sin (π * c.val / 2 ^ (m + 3)) ^ 2 ≤ 2 ^ m :=
    mul_le_of_le_one_right (by positivity) h1
  rw [Nat.floor_lt (by positivity)]
  have h3 : (((2 ^ (m + 3) : ℕ)) : ℝ) = 8 * 2 ^ m := by push_cast; ring
  rw [h3]
  linarith

noncomputable def rr (m : ℕ) (c : Fin (2 ^ (m + 3))) : Fin (2 ^ (m + 3)) := ⟨rv m c, rv_lt m c⟩

/-- `o ↦ o + rr c`. -/
noncomputable def shiftP (n m : ℕ) : Equiv.Perm (PT n m) where
  toFun y := ((y.1.1 + rr m y.1.2, y.1.2), y.2)
  invFun y := ((y.1.1 - rr m y.1.2, y.1.2), y.2)
  left_inv y := by simp
  right_inv y := by simp

/-! ## Unitaries -/

lemma kron_unitary2 {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (A : Matrix I I ℂ) (B : Matrix K K ℂ) (hA : star A * A = 1) (hB : star B * B = 1) :
    star (A ⊗ₖ B) * (A ⊗ₖ B) = 1 := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  rw [Matrix.star_eq_conjTranspose] at hA hB
  rw [hA, hB, Matrix.one_kronecker_one]

lemma one_unitary {I : Type*} [Fintype I] [DecidableEq I] :
    star (1 : Matrix I I ℂ) * 1 = 1 := by simp

lemma mul_unitary {X : Type*} [Fintype X] [DecidableEq X] (P Q : Matrix X X ℂ)
    (hP : star P * P = 1) (hQ : star Q * Q = 1) : star (P * Q) * (P * Q) = 1 := by
  calc star (P * Q) * (P * Q) = star Q * (star P * P) * Q := by
        simp only [star_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hP, Matrix.mul_one, hQ]

lemma kF_unitary (n m : ℕ) (U : Matrix (Fin (2 ^ (m + 3))) (Fin (2 ^ (m + 3))) ℂ)
    (h : star U * U = 1) : star (kF n m U) * kF n m U = 1 :=
  kron_unitary2 _ _ (kron_unitary2 _ _ one_unitary h) one_unitary

lemma Xm_unitary : star Xm * Xm = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xm, Matrix.mul_apply, Fin.sum_univ_two]

lemma flipP_unitary (n m : ℕ) : star (flipP n m) * flipP n m = 1 :=
  kron_unitary2 _ _ one_unitary (kron_unitary2 _ _ one_unitary Xm_unitary)

lemma diag_unitary {X : Type*} [Fintype X] [DecidableEq X] (φ : X → ℂ)
    (h : ∀ x, φ x = 1 ∨ φ x = -1) : star (Matrix.diagonal φ) * Matrix.diagonal φ = 1 := by
  have h1 : (fun x ↦ star (φ x) * φ x) = fun _ ↦ (1 : ℂ) := by
    funext x; rcases h x with h | h <;> simp [h]
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  simp only [Pi.star_apply]
  rw [h1]
  exact Matrix.diagonal_one

lemma aM_unitary (n m : ℕ) (j : Fin (m + 3)) : star (aM n m j) * aM n m j = 1 :=
  mul_unitary _ _ (flipP_unitary n m) (diag_unitary _ fun y ↦ by unfold phA; split_ifs <;> simp)

lemma bM_unitary (n m : ℕ) (j : Fin (m + 3)) : star (bM n m j) * bM n m j = 1 :=
  mul_unitary _ _ (flipP_unitary n m) (diag_unitary _ fun y ↦ by unfold phB; split_ifs <;> simp)

lemma oraP_unitary {n : ℕ} (A : Unitary (2 ^ n)) (m : ℕ) :
    star (oraP A m) * oraP A m = 1 :=
  kron_unitary2 _ _ one_unitary
    (liftMat_star_mul _ _ (Matrix.mem_unitaryGroup_iff'.1 (ampEstOracle A).2))

/-! ## Stage 3: the Grover iterate on `A`'s register -/

/-- Inner product `⟨x, y⟩`, conjugate-linear in `x`. -/
def gram {d : ℕ} (x y : Fin d → ℂ) : ℂ := star x ⬝ᵥ y

lemma gram_unitary {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (hU : star U * U = 1)
    (x y : Fin d → ℂ) : gram (U *ᵥ x) (U *ᵥ y) = gram x y := by
  unfold gram
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose, hU, Matrix.vecMul_one]

lemma gram_conj {d : ℕ} (x y : Fin d → ℂ) : star (gram x y) = gram y x := by
  simp only [gram, dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

section Grover
variable {n : ℕ} (A : Unitary (2 ^ n))

/-- `A |0⟩`. -/
noncomputable def psiV : Fin (2 ^ n) → ℂ := fun x ↦ A.1 x 0

/-- The sign flip on flagged basis states. -/
noncomputable def Dchi (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.diagonal fun x ↦ if x.val % 2 = 1 then -1 else 1

/-- The reflection `-S_0`. -/
noncomputable def Dzero (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.diagonal fun x ↦ if x = 0 then 1 else -1

/-- The Grover iterate. -/
noncomputable def Qm : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  A.1 * Dzero n * star A.1 * Dchi n

lemma Dchi_unit (n : ℕ) : star (Dchi n) * Dchi n = 1 :=
  diag_unitary _ fun x ↦ by by_cases h : x.val % 2 = 1 <;> simp [h]

lemma Dzero_unit (n : ℕ) : star (Dzero n) * Dzero n = 1 :=
  diag_unitary _ fun x ↦ by by_cases h : x = 0 <;> simp [h]

lemma Dchi_sq (n : ℕ) : Dchi n * Dchi n = 1 := by
  unfold Dchi
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext x
  by_cases h : x.val % 2 = 1 <;> simp [h]

lemma A_unit : star A.1 * A.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 A.2

lemma A_unit' : A.1 * star A.1 = 1 := Matrix.mem_unitaryGroup_iff.1 A.2

lemma Qm_unit : star (Qm A) * Qm A = 1 := by
  refine mul_unitary _ _ (mul_unitary _ _ (mul_unitary _ _ (A_unit A) (Dzero_unit n)) ?_)
    (Dchi_unit n)
  simpa using A_unit' A

lemma psi_gram : gram (psiV A) (psiV A) = 1 := by
  have h := congrFun (congrFun (A_unit A) 0) 0
  simpa [Matrix.mul_apply, gram, dotProduct, psiV] using h

lemma Dzero_mulVec (w : Fin (2 ^ n) → ℂ) :
    Dzero n *ᵥ w = (2 * w 0) • (Pi.single 0 1 : Fin (2 ^ n) → ℂ) - w := by
  funext x
  by_cases hx : x = 0
  · subst hx; simp [Dzero, Matrix.mulVec_diagonal]; ring
  · simp [Dzero, Matrix.mulVec_diagonal, hx, Pi.single_apply]

lemma Qm_mulVec (v : Fin (2 ^ n) → ℂ) :
    Qm A *ᵥ v = (2 * gram (psiV A) (Dchi n *ᵥ v)) • psiV A - Dchi n *ᵥ v := by
  have h1 : Qm A *ᵥ v = A.1 *ᵥ (Dzero n *ᵥ (star A.1 *ᵥ (Dchi n *ᵥ v))) := by
    unfold Qm
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have h4 : ∀ u : Fin (2 ^ n) → ℂ, A.1 *ᵥ (star A.1 *ᵥ u) = u := fun u ↦ by
    rw [Matrix.mulVec_mulVec, A_unit', Matrix.one_mulVec]
  rw [h1, Dzero_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, h4]
  have h2 : A.1 *ᵥ (Pi.single 0 1 : Fin (2 ^ n) → ℂ) = psiV A := by
    funext x; simp [Matrix.mulVec, dotProduct, Pi.single_apply, psiV]
  have h3 : (star A.1 *ᵥ (Dchi n *ᵥ v)) 0 = gram (psiV A) (Dchi n *ᵥ v) := by
    simp [Matrix.mulVec, dotProduct, gram, psiV, Matrix.star_apply]
  rw [h2, h3]

end Grover

section Grover2
variable {n : ℕ} (A : Unitary (2 ^ n))

lemma sum_normSq_psi : ∑ x : Fin (2 ^ n), Complex.normSq (psiV A x) = 1 := by
  have h := psi_gram A
  have h2 : ((∑ x : Fin (2 ^ n), Complex.normSq (psiV A x) : ℝ) : ℂ) = 1 := by
    rw [← h, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp [Complex.normSq_eq_conj_mul_self, Pi.star_apply]
  exact_mod_cast h2

lemma amp_eq : ampEstAmplitude A =
    ∑ x : Fin (2 ^ n), if x.val % 2 = 1 then Complex.normSq (psiV A x) else 0 := by
  unfold ampEstAmplitude
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  split_ifs
  · rw [Complex.normSq_eq_norm_sq]; rfl
  · rfl

lemma amp_nonneg : 0 ≤ ampEstAmplitude A := by
  rw [amp_eq]
  exact Finset.sum_nonneg fun x _ ↦ by split_ifs <;> simp [Complex.normSq_nonneg]

lemma amp_le_one : ampEstAmplitude A ≤ 1 := by
  rw [amp_eq, ← sum_normSq_psi A]
  exact Finset.sum_le_sum fun x _ ↦ by split_ifs <;> simp [Complex.normSq_nonneg]

lemma chi_gram : gram (psiV A) (Dchi n *ᵥ psiV A) = ((1 - 2 * ampEstAmplitude A : ℝ) : ℂ) := by
  have h1 : gram (psiV A) (Dchi n *ᵥ psiV A) =
      ((∑ x : Fin (2 ^ n), (if x.val % 2 = 1 then -Complex.normSq (psiV A x)
        else Complex.normSq (psiV A x)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp only [gram, dotProduct, Matrix.mulVec, Dchi, Matrix.diagonal, Matrix.of_apply]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.sum_eq_single x]
    · by_cases h : x.val % 2 = 1 <;>
        simp [h, Complex.normSq_eq_conj_mul_self, Pi.star_apply]
    · intro y _ hy; simp [Ne.symm hy]
    · simp
  rw [h1]
  congr 1
  have h2 : ∑ x : Fin (2 ^ n), (if x.val % 2 = 1 then -Complex.normSq (psiV A x)
        else Complex.normSq (psiV A x)) =
      ∑ x : Fin (2 ^ n), Complex.normSq (psiV A x) -
        2 * ∑ x : Fin (2 ^ n), (if x.val % 2 = 1 then Complex.normSq (psiV A x) else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    split_ifs <;> ring
  rw [h2, sum_normSq_psi, ← amp_eq]

/-- The rotation angle: `cos φ = 1 - 2a`. -/
noncomputable def phiA : ℝ := Real.arccos (1 - 2 * ampEstAmplitude A)

lemma cos_phiA : Real.cos (phiA A) = 1 - 2 * ampEstAmplitude A :=
  Real.cos_arccos (by linarith [amp_le_one A]) (by linarith [amp_nonneg A])

lemma Qm_psi : Qm A *ᵥ psiV A =
    ((2 * Real.cos (phiA A) : ℝ) : ℂ) • psiV A - Dchi n *ᵥ psiV A := by
  rw [Qm_mulVec, chi_gram, cos_phiA]
  push_cast
  ring_nf

lemma Qm_chi : Qm A *ᵥ (Dchi n *ᵥ psiV A) = psiV A := by
  rw [Qm_mulVec, Matrix.mulVec_mulVec, Dchi_sq, Matrix.one_mulVec, psi_gram, mul_one,
    two_smul, add_sub_cancel_right]

end Grover2

section Grover3
variable {n : ℕ} (A : Unitary (2 ^ n))

lemma gram_lin {d : ℕ} (x y z : Fin d → ℂ) (α : ℂ) :
    gram x (α • y - z) = α * gram x y - gram x z := by
  simp [gram, dotProduct_sub, dotProduct_smul]

lemma Qm_rec (k : ℕ) : (Qm A ^ (k + 2)) *ᵥ psiV A =
    ((2 * Real.cos (phiA A) : ℝ) : ℂ) • ((Qm A ^ (k + 1)) *ᵥ psiV A) - (Qm A ^ k) *ᵥ psiV A := by
  have h2 : (Qm A ^ 2) *ᵥ psiV A =
      ((2 * Real.cos (phiA A) : ℝ) : ℂ) • (Qm A *ᵥ psiV A) - psiV A := by
    rw [pow_two, ← Matrix.mulVec_mulVec]
    conv_lhs => rw [Qm_psi]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Qm_chi]
  have : (Qm A ^ (k + 2)) *ᵥ psiV A = (Qm A ^ k) *ᵥ ((Qm A ^ 2) *ᵥ psiV A) := by
    rw [Matrix.mulVec_mulVec, ← pow_add, add_comm]
  rw [this, h2, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_succ]

lemma s_cos (k : ℕ) : gram (psiV A) ((Qm A ^ k) *ᵥ psiV A) =
    ((Real.cos ((k : ℝ) * phiA A) : ℝ) : ℂ) ∧
    gram (psiV A) ((Qm A ^ (k + 1)) *ᵥ psiV A) =
    ((Real.cos (((k : ℝ) + 1) * phiA A) : ℝ) : ℂ) := by
  induction k with
  | zero =>
    refine ⟨by simp [psi_gram], ?_⟩
    simp only [zero_add, pow_one, Nat.cast_zero, one_mul]
    rw [Qm_psi, gram_lin, psi_gram, chi_gram, cos_phiA]
    push_cast; ring
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨by rw [Nat.cast_succ]; exact h1, ?_⟩
    rw [show k + 1 + 1 = k + 2 from rfl, Qm_rec, gram_lin, h0, h1]
    have e1 := Real.cos_add (((k : ℝ) + 1) * phiA A) (phiA A)
    have e2 := Real.cos_sub (((k : ℝ) + 1) * phiA A) (phiA A)
    have e3 : ((k : ℝ) + 1) * phiA A + phiA A = ((k : ℝ) + 1 + 1) * phiA A := by ring
    have e4 : ((k : ℝ) + 1) * phiA A - phiA A = (k : ℝ) * phiA A := by ring
    have e5 : (((k + 1 : ℕ) : ℝ) + 1) = (k : ℝ) + 1 + 1 := by push_cast; ring
    rw [e3] at e1
    rw [e4] at e2
    rw [e5]
    have key : 2 * Real.cos (phiA A) * Real.cos (((k : ℝ) + 1) * phiA A) -
        Real.cos ((k : ℝ) * phiA A) = Real.cos (((k : ℝ) + 1 + 1) * phiA A) := by
      linarith
    exact_mod_cast key

lemma gram_cos (k k' : ℕ) : gram ((Qm A ^ k) *ᵥ psiV A) ((Qm A ^ k') *ᵥ psiV A) =
    ((Real.cos (((k' : ℝ) - k) * phiA A) : ℝ) : ℂ) := by
  induction k generalizing k' with
  | zero => simpa [Matrix.one_mulVec] using (s_cos A k').1
  | succ k ih =>
    cases k' with
    | zero =>
      have h := gram_conj (psiV A) ((Qm A ^ (k + 1)) *ᵥ psiV A)
      rw [(s_cos A (k + 1)).1] at h
      have h' : gram ((Qm A ^ (k + 1)) *ᵥ psiV A) (psiV A) =
          ((Real.cos (((k + 1 : ℕ) : ℝ) * phiA A) : ℝ) : ℂ) := by
        rw [← h]; exact Complex.conj_ofReal _
      have e : (((0 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ)) * phiA A = -(((k + 1 : ℕ) : ℝ) * phiA A) := by
        push_cast; ring
      rw [pow_zero, Matrix.one_mulVec] 
      rw [e, Real.cos_neg]
      exact h'
    | succ k' =>
      rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        gram_unitary _ (Qm_unit A), ih k']
      congr 2
      push_cast; ring

end Grover3

/-! ## Stage 4a: the oracle embedding -/

lemma bit_mod (M j x : ℕ) (hj : j < M) : x % 2 ^ M / 2 ^ j % 2 = x / 2 ^ j % 2 := by
  obtain ⟨d, rfl⟩ : ∃ d, M = j + 1 + d := ⟨M - j - 1, by omega⟩
  have h1 : 2 ^ (j + 1 + d) = 2 ^ j * 2 ^ (d + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [h1, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))

lemma extract_gen {N : ℕ} (off w : ℕ) (h : off + w ≤ N) (g : Fin (2 ^ N)) :
    (((QRegister.block off w h).extractIndex g : Fin (2 ^ w)) : ℕ) = g.val / 2 ^ off % 2 ^ w := by
  have hlt : g.val / 2 ^ off % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
  have key : (QRegister.block off w h).extractIndex g = ⟨g.val / 2 ^ off % 2 ^ w, hlt⟩ := by
    apply (basisBits w).injective
    funext i
    rw [QRegister.basisBits_extractIndex, basisBits_eq_div_mod, basisBits_eq_div_mod]
    congr 1
    show g.val / 2 ^ (off + i.val) % 2 = g.val / 2 ^ off % 2 ^ w / 2 ^ i.val % 2
    rw [bit_mod w i.val _ i.isLt, Nat.div_div_eq_div_mul, pow_add]
  rw [key]

lemma env_gen {N : ℕ} (w : ℕ) (h : 0 + w ≤ N) (x y : Fin (2 ^ N)) :
    ((QRegister.block 0 w h).basisSplitEquiv x).2 = ((QRegister.block 0 w h).basisSplitEquiv y).2 ↔
      x.val / 2 ^ w = y.val / 2 ^ w := by
  rw [QRegister.basisSplit_environment_eq_iff]
  constructor
  · intro hxy
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
    by_cases hi : i + w < N
    · have hq : (⟨i + w, hi⟩ : Fin N) ∉ Set.range (QRegister.block 0 w h).wires := by
        rintro ⟨j, hj⟩
        have h3 : 0 + j.val = i + w := congrArg Fin.val hj
        have := j.isLt
        omega
      have h2 := hxy _ hq
      rw [basisBits_eq_div_mod, basisBits_eq_div_mod] at h2
      have h4 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h2
      simp only [Nat.mod_mod] at h4
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, h4]
    · have hi' : N ≤ i + w := not_lt.1 hi
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by norm_num) hi')),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by norm_num) hi'))]
  · intro hxy q hq
    have hqn : w ≤ q.val := by
      by_contra hc
      exact hq ⟨⟨q.val, by omega⟩, Fin.ext (by show 0 + q.val = q.val; omega)⟩
    rw [basisBits_eq_div_mod, basisBits_eq_div_mod]
    have e : 2 ^ q.val = 2 ^ w * 2 ^ (q.val - w) := by rw [← pow_add]; congr 1; omega
    have : x.val / 2 ^ q.val = y.val / 2 ^ q.val := by
      rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hxy]
    rw [this]

lemma liftMat_apply {X Y : Type*} (e : X ≃ Y) (M : Matrix X X ℂ) (x x' : X) :
    liftMat e M (e x) (e x') = M x x' := by simp [liftMat]

lemma eP_split (n m : ℕ) (o c : Fin (2 ^ (m + 3))) (a : Fin (2 ^ n)) (s : Fin 2) :
    (eP n m ((o, c), (a, s))).val % 2 ^ (n + 1) = s.val + 2 * a.val ∧
    (eP n m ((o, c), (a, s))).val / 2 ^ (n + 1) = c.val + 2 ^ (m + 3) * o.val := by
  rw [eP_val]
  have ha := a.isLt
  have hs := s.isLt
  have hp : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
  have hlt : s.val + 2 * a.val < 2 ^ n * 2 := by omega
  rw [hp]
  constructor
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]

lemma oracle_entry2 {n : ℕ} (A : Unitary (2 ^ n)) (a a' : Fin (2 ^ n)) (s s' : Fin 2) :
    (ampEstOracle A).1 (finProdFinEquiv (a, s)) (finProdFinEquiv (a', s')) =
      if s = s' then ampEstBlocks A s a a' else 0 := by
  show (Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Matrix.blockDiagonal (ampEstBlocks A))) _ _ = _
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  simp only [Equiv.symm_apply_apply, Matrix.blockDiagonal_apply]

lemma cond_iff (m : ℕ) (o c o' c' : Fin (2 ^ (m + 3))) :
    c.val + 2 ^ (m + 3) * o.val = c'.val + 2 ^ (m + 3) * o'.val ↔ (o = o' ∧ c = c') := by
  constructor
  · intro h
    have h' : finProdFinEquiv (o, c) = finProdFinEquiv (o', c') :=
      Fin.ext (by simpa [finProdFinEquiv] using h)
    simpa [Prod.ext_iff] using finProdFinEquiv.injective h'
  · rintro ⟨rfl, rfl⟩; rfl

lemma embed_eq {n : ℕ} (A : Unitary (2 ^ n)) (m : ℕ) :
    (regO n m).embedMatrix (ampEstOracle A).1 = liftMat (eP n m) (oraP A m) := by
  ext g g'
  obtain ⟨y, rfl⟩ := (eP n m).surjective g
  obtain ⟨y', rfl⟩ := (eP n m).surjective g'
  obtain ⟨⟨o, c⟩, ⟨a, s⟩⟩ := y
  obtain ⟨⟨o', c'⟩, ⟨a', s'⟩⟩ := y'
  rw [liftMat_apply, QRegister.embedMatrix_apply]
  unfold regO
  simp only [env_gen]
  obtain ⟨h1, h2⟩ := eP_split n m o c a s
  obtain ⟨h1', h2'⟩ := eP_split n m o' c' a' s'
  have e1 : ((QRegister.block 0 (n + 1) (by unfold qq; omega)).extractIndex
      (eP n m ((o, c), (a, s))) : ℕ) = s.val + 2 * a.val := by
    rw [extract_gen, pow_zero, Nat.div_one]; exact h1
  have e1' : ((QRegister.block 0 (n + 1) (by unfold qq; omega)).extractIndex
      (eP n m ((o', c'), (a', s'))) : ℕ) = s'.val + 2 * a'.val := by
    rw [extract_gen, pow_zero, Nat.div_one]; exact h1'
  have x1 : (QRegister.block 0 (n + 1) (by unfold qq; omega)).extractIndex
      (eP n m ((o, c), (a, s))) = (finProdFinEquiv (a, s) : Fin (2 ^ n * 2)) :=
    Fin.ext (by rw [e1]; simp [finProdFinEquiv])
  have x1' : (QRegister.block 0 (n + 1) (by unfold qq; omega)).extractIndex
      (eP n m ((o', c'), (a', s'))) = (finProdFinEquiv (a', s') : Fin (2 ^ n * 2)) :=
    Fin.ext (by rw [e1']; simp [finProdFinEquiv])
  simp only [x1, x1', h2, h2', cond_iff]
  simp only [oraP, liftMat, Matrix.kroneckerMap_apply, Matrix.one_apply, Equiv.symm_symm,
    Prod.mk.injEq]
  by_cases hh : o = o' ∧ c = c'
  · simp [hh]; rfl
  · simp [hh]

/-! ## Stage 4b: action of the step matrices on states -/

lemma inv_val_eq {n : ℕ} (A : Unitary (2 ^ n)) : (A⁻¹).1 = star A.1 := rfl

lemma kron_one_mulVec {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (B : Matrix K K ℂ) (u : I × K → ℂ) (x : I) (y : K) :
    (((1 : Matrix I I ℂ) ⊗ₖ B) *ᵥ u) (x, y) = ∑ y', B y y' * u (x, y') := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply]
  simp [ite_mul, Finset.sum_ite_eq]

lemma kron_one_right_mulVec {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (B : Matrix I I ℂ) (u : I × K → ℂ) (x : I) (y : K) :
    ((B ⊗ₖ (1 : Matrix K K ℂ)) *ᵥ u) (x, y) = ∑ x', B x x' * u (x', y) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply]
  simp [mul_ite, Finset.sum_ite_eq]

lemma kF_mulVec (n m : ℕ) (U : Matrix (Fin (2 ^ (m + 3))) (Fin (2 ^ (m + 3))) ℂ)
    (u : PT n m → ℂ) (o c : Fin (2 ^ (m + 3))) (r : Fin (2 ^ n) × Fin 2) :
    (kF n m U *ᵥ u) ((o, c), r) = ∑ c', U c c' * u ((o, c'), r) := by
  unfold kF
  rw [kron_one_right_mulVec]
  simp [Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul,
    Finset.sum_ite_eq]

lemma flipP_mulVec (n m : ℕ) (u : PT n m → ℂ) (o c : Fin (2 ^ (m + 3))) (a : Fin (2 ^ n))
    (s : Fin 2) :
    (flipP n m *ᵥ u) ((o, c), (a, s)) = ∑ s', Xm s s' * u ((o, c), (a, s')) := by
  unfold flipP
  rw [kron_one_mulVec]
  simp [Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul,
    Finset.sum_ite_eq]

lemma liftMat_fpf {n : ℕ} (A : Unitary (2 ^ n)) (a a' : Fin (2 ^ n)) (s s' : Fin 2) :
    liftMat (finProdFinEquiv.symm : Fin (2 ^ n * 2) ≃ Fin (2 ^ n) × Fin 2) (ampEstOracle A).1
      (a, s) (a', s') = (ampEstOracle A).1 (finProdFinEquiv (a, s)) (finProdFinEquiv (a', s')) := by
  unfold liftMat
  rfl

lemma oraP_mulVec {n : ℕ} (A : Unitary (2 ^ n)) (m : ℕ) (u : PT n m → ℂ)
    (o c : Fin (2 ^ (m + 3))) (a : Fin (2 ^ n)) (s : Fin 2) :
    (oraP A m *ᵥ u) ((o, c), (a, s)) = ∑ a', ampEstBlocks A s a a' * u ((o, c), (a', s)) := by
  unfold oraP
  rw [kron_one_mulVec]
  simp only [Fintype.sum_prod_type, liftMat_fpf, oracle_entry2, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]


/-- States with select bit `0`. -/
def emb {n : ℕ} (m : ℕ) (g : Fin (2 ^ (m + 3)) × Fin (2 ^ (m + 3)) → Fin (2 ^ n) → ℂ) :
    PT n m → ℂ := fun y ↦ if y.2.2 = 0 then g y.1 y.2.1 else 0

/-- States with select bit `1`. -/
def emb1 {n : ℕ} (m : ℕ) (g : Fin (2 ^ (m + 3)) × Fin (2 ^ (m + 3)) → Fin (2 ^ n) → ℂ) :
    PT n m → ℂ := fun y ↦ if y.2.2 = 1 then g y.1 y.2.1 else 0

lemma kF_emb {n : ℕ} (m : ℕ) (U : Matrix (Fin (2 ^ (m + 3))) (Fin (2 ^ (m + 3))) ℂ)
    (g : Fin (2 ^ (m + 3)) × Fin (2 ^ (m + 3)) → Fin (2 ^ n) → ℂ) :
    kF n m U *ᵥ emb m g = emb m (fun oc a ↦ ∑ c', U oc.2 c' * g (oc.1, c') a) := by
  ext ⟨⟨o, c⟩, ⟨a, s⟩⟩
  rw [kF_mulVec]
  by_cases hs : s = 0 <;> simp [emb, hs]

lemma ora_emb {n : ℕ} (A : Unitary (2 ^ n)) (m : ℕ)
    (g : Fin (2 ^ (m + 3)) × Fin (2 ^ (m + 3)) → Fin (2 ^ n) → ℂ) :
    oraP A m *ᵥ emb m g = emb m (fun oc ↦ A.1 *ᵥ g oc) := by
  ext ⟨⟨o, c⟩, ⟨a, s⟩⟩
  rw [oraP_mulVec]
  by_cases hs : s = 0
  · subst hs
    simp [emb, ampEstBlocks, Matrix.mulVec, dotProduct]
  · simp [emb, hs]

lemma ora_emb1 {n : ℕ} (A : Unitary (2 ^ n)) (m : ℕ)
    (g : Fin (2 ^ (m + 3)) × Fin (2 ^ (m + 3)) → Fin (2 ^ n) → ℂ) :
    oraP A m *ᵥ emb1 m g = emb1 m (fun oc ↦ star A.1 *ᵥ g oc) := by
  ext ⟨⟨o, c⟩, ⟨a, s⟩⟩
  rw [oraP_mulVec]
  by_cases hs : s = 1
  · subst hs
    simp [emb1, ampEstBlocks, inv_val_eq, Matrix.mulVec, dotProduct]
  · simp [emb1, hs]

def sgnA (b : ℕ) (a : Fin (2 ^ n)) : ℂ := if b = 1 ∧ a.val % 2 = 1 then -1 else 1

def sgnB (b : ℕ) (a : Fin (2 ^ n)) : ℂ := if b = 1 ∧ a ≠ 0 then -1 else 1

lemma aM_emb {n : ℕ} (m : ℕ) (j : Fin (m + 3))
    (g : Fin (2 ^ (m + 3)) × Fin (2 ^ (m + 3)) → Fin (2 ^ n) → ℂ) :
    aM n m j *ᵥ emb m g = emb1 m (fun oc a ↦ sgnA (bitN j oc.2) a * g oc a) := by
  ext ⟨⟨o, c⟩, ⟨a, s⟩⟩
  unfold aM
  rw [← Matrix.mulVec_mulVec, flipP_mulVec]
  fin_cases s <;>
    simp [Matrix.mulVec_diagonal, Fin.sum_univ_two, emb, emb1, Xm, phA, sgnA]

lemma bM_emb1 {n : ℕ} (m : ℕ) (j : Fin (m + 3))
    (g : Fin (2 ^ (m + 3)) × Fin (2 ^ (m + 3)) → Fin (2 ^ n) → ℂ) :
    bM n m j *ᵥ emb1 m g = emb m (fun oc a ↦ sgnB (bitN j oc.2) a * g oc a) := by
  ext ⟨⟨o, c⟩, ⟨a, s⟩⟩
  unfold bM
  rw [← Matrix.mulVec_mulVec, flipP_mulVec]
  fin_cases s <;>
    simp [Matrix.mulVec_diagonal, Fin.sum_univ_two, emb, emb1, Xm, phB, sgnB]

/-- One block: `A_j`, oracle, `B_j`, oracle. -/
noncomputable def blkMat {n : ℕ} (A : Unitary (2 ^ n)) (m : ℕ) (j : Fin (m + 3)) :
    Matrix (PT n m) (PT n m) ℂ :=
  oraP A m * bM n m j * oraP A m * aM n m j

/-- `Q` or the identity, according to a bit. -/
noncomputable def Qb {n : ℕ} (A : Unitary (2 ^ n)) (b : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  if b = 1 then Qm A else 1

lemma blk_vec {n : ℕ} (A : Unitary (2 ^ n)) (b : ℕ) (v : Fin (2 ^ n) → ℂ) :
    A.1 *ᵥ (fun a ↦ sgnB b a * (star A.1 *ᵥ (fun a ↦ sgnA b a * v a)) a) = Qb A b *ᵥ v := by
  have h4 : ∀ u : Fin (2 ^ n) → ℂ, A.1 *ᵥ (star A.1 *ᵥ u) = u := fun u ↦ by
    rw [Matrix.mulVec_mulVec, A_unit', Matrix.one_mulVec]
  unfold Qb
  by_cases hb : b = 1
  · subst hb
    have e1 : (fun a : Fin (2 ^ n) ↦ sgnA 1 a * v a) = Dchi n *ᵥ v := by
      ext a; by_cases h : a.val % 2 = 1 <;> simp [sgnA, Dchi, Matrix.mulVec_diagonal, h]
    have e2 : ∀ w : Fin (2 ^ n) → ℂ, (fun a ↦ sgnB 1 a * w a) = Dzero n *ᵥ w := by
      intro w; ext a; by_cases h : a = 0 <;> simp [sgnB, Dzero, Matrix.mulVec_diagonal, h]
    rw [e1, e2]
    simp only [if_true]
    unfold Qm
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  · have e1 : (fun a : Fin (2 ^ n) ↦ sgnA b a * v a) = v := by
      ext a; simp [sgnA, hb]
    have e2 : ∀ w : Fin (2 ^ n) → ℂ, (fun a ↦ sgnB b a * w a) = w := by
      intro w; ext a; simp [sgnB, hb]
    rw [e1, e2, h4]
    simp [hb]

lemma blk_emb {n : ℕ} (A : Unitary (2 ^ n)) (m : ℕ) (j : Fin (m + 3))
    (g : Fin (2 ^ (m + 3)) × Fin (2 ^ (m + 3)) → Fin (2 ^ n) → ℂ) :
    blkMat A m j *ᵥ emb m g = emb m (fun oc ↦ Qb A (bitN j oc.2) *ᵥ g oc) := by
  unfold blkMat
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, aM_emb, ora_emb1,
    bM_emb1, ora_emb]
  congr 1
  funext oc
  exact blk_vec A _ _

/-- The matrix of a list of blocks. -/
noncomputable def callsP {n : ℕ} (A : Unitary (2 ^ n)) (m : ℕ) :
    List (Fin (m + 3)) → Matrix (PT n m) (PT n m) ℂ
  | [] => 1
  | j :: l => callsP A m l * blkMat A m j

lemma calls_emb {n : ℕ} (A : Unitary (2 ^ n)) (m : ℕ) (l : List (Fin (m + 3)))
    (g : Fin (2 ^ (m + 3)) × Fin (2 ^ (m + 3)) → Fin (2 ^ n) → ℂ) :
    callsP A m l *ᵥ emb m g =
      emb m (fun oc ↦ (Qm A ^ ((l.map fun j ↦ bitN j oc.2).sum)) *ᵥ g oc) := by
  induction l generalizing g with
  | nil => simp [callsP]
  | cons j l ih =>
    rw [callsP, ← Matrix.mulVec_mulVec, blk_emb, ih]
    congr 1
    funext oc
    rw [Matrix.mulVec_mulVec, List.map_cons, List.sum_cons]
    congr 1
    unfold Qb
    have hb : bitN j oc.2 = 0 ∨ bitN j oc.2 = 1 := by unfold bitN; omega
    rcases hb with hb | hb
    · simp [hb]
    · simp [hb]
      generalize (List.map (fun j ↦ bitN j oc.2) l).sum = k
      rw [Nat.add_comm 1 k, pow_succ]

/-! ## Stage 4c: the state before measurement -/

lemma eP_zero (n m : ℕ) :
    eP n m ((0, 0), (0, 0)) = (0 : Fin (2 ^ qq n m)) := by
  apply Fin.ext
  rw [eP_val]
  simp

lemma extractR {n : ℕ} (m : ℕ) (o c : Fin (2 ^ (m + 3))) (a : Fin (2 ^ n)) (s : Fin 2) :
    (((regR n m).extractIndex (eP n m ((o, c), (a, s))) : Fin (2 ^ (m + 3))) : ℕ) = o.val := by
  unfold regR
  rw [extract_gen, show 2 ^ (n + 1 + (m + 3)) = 2 ^ (n + 1) * 2 ^ (m + 3) from pow_add _ _ _,
    ← Nat.div_div_eq_div_mul, (eP_split n m o c a s).2, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt c.isLt, zero_add, Nat.mod_eq_of_lt o.isLt]

/-- The Fourier matrix on the counting register. -/
noncomputable abbrev qf (m : ℕ) : Matrix (Fin (2 ^ (m + 3))) (Fin (2 ^ (m + 3))) ℂ :=
  QFT.qftMatrix (m + 3)

noncomputable def Kc (m : ℕ) (c c' : Fin (2 ^ (m + 3))) : ℂ := star (qf m) c c' * qf m c' 0

/-- The `A`-register amplitude of the outcome `c`. -/
noncomputable def wv {n : ℕ} (A : Unitary (2 ^ n)) (m : ℕ) (c : Fin (2 ^ (m + 3))) :
    Fin (2 ^ n) → ℂ :=
  fun a ↦ ∑ c', Kc m c c' * ((Qm A ^ c'.val) *ᵥ psiV A) a

/-- The whole circuit on the basis `PT`. -/
noncomputable def Tp {n : ℕ} (A : Unitary (2 ^ n)) (m : ℕ) : Matrix (PT n m) (PT n m) ℂ :=
  permMat (shiftP n m) * kF n m (star (qf m)) * callsP A m (oracleCalls (m + 3)) * oraP A m *
    kF n m (qf m)

lemma mulVec_const_mul {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (k : ℂ) (v : Fin d → ℂ) :
    M *ᵥ (fun a ↦ k * v a) = fun a ↦ k * (M *ᵥ v) a := by
  ext a
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]

lemma mulVec_single_const {n : ℕ} (A : Unitary (2 ^ n)) (k : ℂ) :
    A.1 *ᵥ (fun a ↦ k * (Pi.single (0 : Fin (2 ^ n)) (1 : ℂ) : Fin (2 ^ n) → ℂ) a) =
      fun a ↦ k * psiV A a := by
  ext a
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, psiV, mul_comm]

lemma Tp_apply {n : ℕ} (A : Unitary (2 ^ n)) (m : ℕ) (o c : Fin (2 ^ (m + 3)))
    (a : Fin (2 ^ n)) (s : Fin 2) :
    (Tp A m *ᵥ (Pi.single ((0, 0), (0, 0)) (1 : ℂ) : PT n m → ℂ)) ((o, c), (a, s)) =
      if s = 0 ∧ o = rr m c then wv A m c a else 0 := by
  have h1 : kF n m (qf m) *ᵥ (Pi.single ((0, 0), (0, 0)) (1 : ℂ) : PT n m → ℂ) =
      emb m (fun oc a ↦ (if oc.1 = 0 then qf m oc.2 0 else 0) *
        (Pi.single (0 : Fin (2 ^ n)) (1 : ℂ) : Fin (2 ^ n) → ℂ) a) := by
    ext ⟨⟨o, c⟩, ⟨a, s⟩⟩
    rw [kF_mulVec]
    by_cases ho : o = 0 <;> by_cases ha : a = 0 <;> by_cases hs : s = 0 <;>
      simp [emb, Pi.single_apply, Prod.ext_iff, ho, ha, hs]
  have h2 : oraP A m *ᵥ emb m (fun oc a ↦ (if oc.1 = 0 then qf m oc.2 0 else 0) *
        (Pi.single (0 : Fin (2 ^ n)) (1 : ℂ) : Fin (2 ^ n) → ℂ) a) =
      emb m (fun oc a ↦ (if oc.1 = 0 then qf m oc.2 0 else 0) * psiV A a) := by
    rw [ora_emb]
    congr 1
    funext oc
    exact mulVec_single_const A _
  have h3 : callsP A m (oracleCalls (m + 3)) *ᵥ
      emb m (fun oc a ↦ (if oc.1 = 0 then qf m oc.2 0 else 0) * psiV A a) =
      emb m (fun oc a ↦ (if oc.1 = 0 then qf m oc.2 0 else 0) *
        ((Qm A ^ oc.2.val) *ᵥ psiV A) a) := by
    rw [calls_emb]
    congr 1
    funext oc
    rw [sum_oracleCalls, mulVec_const_mul]
  have h4 : kF n m (star (qf m)) *ᵥ
      emb m (fun oc a ↦ (if oc.1 = 0 then qf m oc.2 0 else 0) *
        ((Qm A ^ oc.2.val) *ᵥ psiV A) a) =
      emb m (fun oc a ↦ if oc.1 = 0 then wv A m oc.2 a else 0) := by
    rw [kF_emb]
    congr 1
    funext oc a
    by_cases ho : oc.1 = 0
    · simp [ho, wv, Kc, mul_assoc]
    · simp [ho]
  simp only [Tp, ← Matrix.mulVec_mulVec]
  rw [h1, h2, h3, h4, permMat_mulVec]
  show emb m _ (((o - rr m c, c), (a, s))) = _
  by_cases hs : s = 0
  · simp [emb, hs]
    by_cases h : o = rr m c
    · simp [h]
    · have h' : ¬ (o - rr m c = 0) := fun h' ↦ h (sub_eq_zero.1 h')
      simp [h, h']
  · simp [emb, hs]

/-! ## Stage 4d: the outcome distribution -/

lemma gram_sum {N d : ℕ} (K : Fin N → ℂ) (v : Fin N → Fin d → ℂ) :
    gram (fun a ↦ ∑ c, K c * v c a) (fun a ↦ ∑ c, K c * v c a) =
      ∑ c', ∑ c'', star (K c') * K c'' * gram (v c') (v c'') := by
  unfold gram dotProduct
  simp only [Pi.star_apply, star_sum, star_mul', Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun c' _ ↦ ?_)
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun c'' _ ↦ ?_)
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  ring

lemma gram_self_re {d : ℕ} (x : Fin d → ℂ) :
    gram x x = ((∑ a, Complex.normSq (x a) : ℝ) : ℂ) := by
  unfold gram dotProduct
  push_cast
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

/-- `exp (i k ω)`. -/
noncomputable def Ex (ω : ℝ) (k : ℕ) : ℂ := Complex.exp ((((k : ℝ) * ω : ℝ) : ℂ) * Complex.I)

lemma star_Ex (ω : ℝ) (k : ℕ) : star (Ex ω k) = Ex (-ω) k := by
  unfold Ex
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I]

lemma Ex_mul_star (ω : ℝ) (k k' : ℕ) :
    Ex ω k' * star (Ex ω k) = Complex.exp ((((k' : ℝ) - k) * ω : ℝ) * Complex.I) := by
  rw [star_Ex, Ex, Ex, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma cos_ex (φ : ℝ) (k k' : ℕ) :
    ((Real.cos (((k' : ℝ) - k) * φ) : ℝ) : ℂ) =
      (Ex φ k' * star (Ex φ k) + Ex (-φ) k' * star (Ex (-φ) k)) / 2 := by
  rw [Ex_mul_star, Ex_mul_star, Complex.ofReal_cos, Complex.cos]
  have h : (((k' : ℝ) - k) * (-φ) : ℝ) = -(((k' : ℝ) - k) * φ) := by ring
  rw [h, Complex.ofReal_neg]

lemma S_sq {N : ℕ} (K E : Fin N → ℂ) :
    star (∑ c, K c * E c) * (∑ c, K c * E c) =
      ∑ c', ∑ c'', star (K c') * K c'' * (E c'' * star (E c')) := by
  rw [star_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun c' _ ↦ Finset.sum_congr rfl fun c'' _ ↦ ?_
  rw [star_mul']
  ring

lemma phaseZ_pow (φ : ℝ) (k : ℕ) : phaseZ (φ / (2 * π)) ^ k = Ex φ k := by
  unfold phaseZ Ex
  rw [← Complex.exp_nat_mul]
  congr 1
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

lemma Wm_entry (c : Fin (2 ^ (m + 3))) (θ : ℝ) :
    Wm (m + 3) θ c 0 = ∑ c', Kc m c c' * phaseZ θ ^ c'.val := by
  unfold Wm
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.star_apply]
  refine Finset.sum_congr rfl fun c' _ ↦ ?_
  simp only [Kc, qf, Matrix.star_apply]
  ring

lemma wv_prob {n : ℕ} (A : Unitary (2 ^ n)) (c : Fin (2 ^ (m + 3))) :
    ∑ a, Complex.normSq (wv A m c a) =
      (Complex.normSq (Wm (m + 3) (phiA A / (2 * π)) c 0) +
        Complex.normSq (Wm (m + 3) (-(phiA A / (2 * π))) c 0)) / 2 := by
  apply Complex.ofReal_injective
  have h1 := gram_self_re (wv A m c)
  have h2 : gram (wv A m c) (wv A m c) = ∑ c', ∑ c'', star (Kc m c c') * Kc m c c'' *
      (((Real.cos (((c''.val : ℕ) - (c'.val : ℕ) : ℝ) * phiA A) : ℝ) : ℂ)) := by
    unfold wv
    rw [gram_sum]
    refine Finset.sum_congr rfl fun c' _ ↦ Finset.sum_congr rfl fun c'' _ ↦ ?_
    rw [gram_cos]
  rw [← h1, h2]
  have e1 : ∀ ω : ℝ, ((Complex.normSq (Wm (m + 3) (ω / (2 * π)) c 0) : ℝ) : ℂ) =
      ∑ c', ∑ c'', star (Kc m c c') * Kc m c c'' * (Ex ω c''.val * star (Ex ω c'.val)) := by
    intro ω
    rw [Complex.normSq_eq_conj_mul_self, Wm_entry]
    have : ∀ c' : Fin (2 ^ (m + 3)), phaseZ (ω / (2 * π)) ^ c'.val = Ex ω c'.val :=
      fun c' ↦ phaseZ_pow ω _
    simp only [this]
    rw [Complex.star_def.symm]
    exact S_sq _ _
  have e2 : ((Complex.normSq (Wm (m + 3) (-(phiA A / (2 * π))) c 0) : ℝ) : ℂ) =
      ∑ c', ∑ c'', star (Kc m c c') * Kc m c c'' *
        (Ex (-phiA A) c''.val * star (Ex (-phiA A) c'.val)) := by
    rw [← neg_div]
    exact e1 (-phiA A)
  rw [Complex.ofReal_div, Complex.ofReal_add, e1, e2, Complex.ofReal_ofNat]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun c' _ ↦ ?_
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun c'' _ ↦ ?_
  rw [cos_ex]
  ring

/-! ## Stage 5: the trigonometric error bound -/

lemma sin_sq_eq (z : ℝ) : Real.sin z ^ 2 = (1 - Real.cos (2 * z)) / 2 := by
  rw [Real.cos_two_mul, Real.sin_sq]; ring

lemma sin_sq_lip (x y : ℝ) : |Real.sin x ^ 2 - Real.sin y ^ 2| ≤ |x - y| := by
  rw [sin_sq_eq, sin_sq_eq]
  have := Real.abs_cos_sub_cos_le (2 * y) (2 * x)
  have e : (1 - Real.cos (2 * x)) / 2 - (1 - Real.cos (2 * y)) / 2 =
      (Real.cos (2 * y) - Real.cos (2 * x)) / 2 := by ring
  rw [e, abs_div, abs_two]
  calc |Real.cos (2 * y) - Real.cos (2 * x)| / 2 ≤ |2 * y - 2 * x| / 2 := by gcongr
    _ = |x - y| := by
      rw [show 2 * y - 2 * x = -(2 * (x - y)) by ring, abs_neg, abs_mul, abs_two]; ring

lemma trig_bound (m : ℕ) (a θ : ℝ) (ha : Real.sin (π * θ) ^ 2 = a) (y : Fin (2 ^ (m + 3)))
    (h : IsPhaseEstimate (m + 3) θ (y.val : ℤ)) :
    |a - (rv m y : ℝ) / 2 ^ m| ≤ 1 / 2 ^ m := by
  obtain ⟨j, hj⟩ := h
  have hj' : |θ - (y.val : ℝ) / 2 ^ (m + 3) - j| ≤ 1 / 2 ^ (m + 3) := by simpa using hj
  have hP : (0 : ℝ) < 2 ^ m := by positivity
  have hM : (2 : ℝ) ^ (m + 3) = 8 * 2 ^ m := by rw [pow_add]; ring
  have hM0 : (0 : ℝ) < 2 ^ (m + 3) := by positivity
  have h1 : |a - Real.sin (π * y.val / 2 ^ (m + 3)) ^ 2| ≤ π / 2 ^ (m + 3) := by
    have l := sin_sq_lip (π * θ) (π * ((y.val : ℝ) / 2 ^ (m + 3)) + j * π)
    have per : Real.sin (π * ((y.val : ℝ) / 2 ^ (m + 3)) + j * π) ^ 2 =
        Real.sin (π * y.val / 2 ^ (m + 3)) ^ 2 := by
      rw [sin_sq_eq, sin_sq_eq]
      have e : 2 * (π * ((y.val : ℝ) / 2 ^ (m + 3)) + j * π) =
          2 * (π * y.val / 2 ^ (m + 3)) + j * (2 * π) := by ring
      rw [e, Real.cos_add_int_mul_two_pi]
    rw [ha, per] at l
    have e2 : |π * θ - (π * ((y.val : ℝ) / 2 ^ (m + 3)) + j * π)| =
        π * |θ - (y.val : ℝ) / 2 ^ (m + 3) - j| := by
      rw [show π * θ - (π * ((y.val : ℝ) / 2 ^ (m + 3)) + j * π) =
        π * (θ - (y.val : ℝ) / 2 ^ (m + 3) - j) by ring, abs_mul, abs_of_pos Real.pi_pos]
    rw [e2] at l
    calc _ ≤ _ := l
      _ ≤ π * (1 / 2 ^ (m + 3)) := by gcongr
      _ = π / 2 ^ (m + 3) := by ring
  have hfl1 : (rv m y : ℝ) ≤ 2 ^ m * Real.sin (π * y.val / 2 ^ (m + 3)) ^ 2 + 1 / 2 :=
    Nat.floor_le (by positivity)
  have hfl2 : 2 ^ m * Real.sin (π * y.val / 2 ^ (m + 3)) ^ 2 + 1 / 2 < (rv m y : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have h2 : |(rv m y : ℝ) / 2 ^ m - Real.sin (π * y.val / 2 ^ (m + 3)) ^ 2| ≤ 1 / (2 * 2 ^ m) := by
    have key : |(rv m y : ℝ) - 2 ^ m * Real.sin (π * y.val / 2 ^ (m + 3)) ^ 2| ≤ 1 / 2 :=
      abs_le.2 ⟨by linarith, by linarith⟩
    rw [show (rv m y : ℝ) / 2 ^ m - Real.sin (π * y.val / 2 ^ (m + 3)) ^ 2 =
      ((rv m y : ℝ) - 2 ^ m * Real.sin (π * y.val / 2 ^ (m + 3)) ^ 2) / 2 ^ m by
        field_simp, abs_div, abs_of_pos hP]
    rw [← div_div]
    exact div_le_div_of_nonneg_right key hP.le
  have h3 : π / 2 ^ (m + 3) ≤ 1 / (2 * 2 ^ m) := by
    rw [hM, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Real.pi_le_four, hP]
  have h4 : 1 / (2 * (2 : ℝ) ^ m) + 1 / (2 * 2 ^ m) = 1 / 2 ^ m := by field_simp; ring
  calc |a - (rv m y : ℝ) / 2 ^ m|
      = |(a - Real.sin (π * y.val / 2 ^ (m + 3)) ^ 2) +
          (Real.sin (π * y.val / 2 ^ (m + 3)) ^ 2 - (rv m y : ℝ) / 2 ^ m)| := by ring_nf
    _ ≤ |a - Real.sin (π * y.val / 2 ^ (m + 3)) ^ 2| +
          |Real.sin (π * y.val / 2 ^ (m + 3)) ^ 2 - (rv m y : ℝ) / 2 ^ m| := abs_add_le _ _
    _ ≤ 1 / 2 ^ m := by
      rw [abs_sub_comm (Real.sin _ ^ 2)] at *
      linarith

lemma sin_phiA {n : ℕ} (A : Unitary (2 ^ n)) :
    Real.sin (π * (phiA A / (2 * π))) ^ 2 = ampEstAmplitude A := by
  have e : π * (phiA A / (2 * π)) = phiA A / 2 := by
    have := Real.pi_pos.ne'
    field_simp
  rw [e, sin_sq_eq, show 2 * (phiA A / 2) = phiA A by ring, cos_phiA]
  ring

lemma sin_phiA_neg {n : ℕ} (A : Unitary (2 ^ n)) :
    Real.sin (π * (-(phiA A / (2 * π)))) ^ 2 = ampEstAmplitude A := by
  rw [mul_neg, Real.sin_neg, neg_sq, sin_phiA]
/-! ## Stage 6: the weakest precondition and the triple -/

/-- The condition on an output value. -/
def GoodZ (a : ℝ) (m : ℕ) (v : ℤ) : Prop := |a - (v : ℝ) / (2 : ℝ) ^ m| ≤ 1 / (2 : ℝ) ^ m

open scoped Classical in
noncomputable instance (a : ℝ) (m : ℕ) (v : ℤ) : Decidable (GoodZ a m v) := by
  unfold GoodZ; infer_instance

lemma liftMat_one {X Y : Type*} [DecidableEq X] [DecidableEq Y] (e : X ≃ Y) :
    liftMat e (1 : Matrix X X ℂ) = 1 := by
  unfold liftMat; exact Matrix.submatrix_one_equiv e.symm

lemma liftMat_star {X Y : Type*} (e : X ≃ Y) (M : Matrix X X ℂ) :
    liftMat e (star M) = star (liftMat e M) := by
  unfold liftMat
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix]

open scoped Classical in
lemma meas_mat' {n w : ℕ} (r : QRegister w n) (a : ℝ) (m : ℕ) (σ : Store Var) :
    ((wp (QProg.measureRegister res r : QProg Var (2 ^ n))
      (fun σ ↦ ⌜GoodZ a m (σ res)⌝)) σ).1.mat =
      Matrix.diagonal (fun g : Fin (2 ^ n) ↦
        if GoodZ a m ((r.extractIndex g).val : ℤ) then 1 else 0) := by
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

lemma entry_gen {X : Type*} [Fintype X] [DecidableEq X] (T : Matrix X X ℂ) (P : X → Prop)
    [DecidablePred P] (x : X) :
    (star T * Matrix.diagonal (fun y ↦ if P y then (1 : ℂ) else 0) * T) x x =
      ((∑ y, if P y then Complex.normSq (T y x) else 0 : ℝ) : ℂ) := by
  rw [Matrix.mul_apply, Complex.ofReal_sum]
  simp only [Matrix.mul_diagonal, Matrix.star_apply]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  split_ifs <;> simp [Complex.normSq_eq_conj_mul_self]

lemma lift00 {n : ℕ} (m : ℕ) (M : Matrix (PT n m) (PT n m) ℂ) :
    liftMat (eP n m) M 0 0 = M ((0, 0), (0, 0)) ((0, 0), (0, 0)) := by
  rw [← eP_zero n m]
  exact liftMat_apply _ _ _ _

lemma mulVec_single_apply' {X : Type*} [Fintype X] [DecidableEq X] (M : Matrix X X ℂ) (z f : X) :
    (M *ᵥ Pi.single z (1 : ℂ)) f = M f z := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

open scoped Classical in
/-- The success probability. -/
noncomputable def probA {n : ℕ} (A : Unitary (2 ^ n)) (m : ℕ) : ℝ :=
  ∑ c : Fin (2 ^ (m + 3)),
    if GoodZ (ampEstAmplitude A) m ((rr m c).val : ℤ) then
      ∑ a, Complex.normSq (wv A m c a) else 0

open scoped Classical in
lemma sum_formula {n : ℕ} (A : Unitary (2 ^ n)) (m : ℕ) :
    (∑ y : PT n m, if GoodZ (ampEstAmplitude A) m (y.1.1.val : ℤ) then
        Complex.normSq (Tp A m y ((0, 0), (0, 0))) else 0) = probA A m := by
  have hT : ∀ y : PT n m, Tp A m y ((0, 0), (0, 0)) =
      (Tp A m *ᵥ (Pi.single ((0, 0), (0, 0)) (1 : ℂ) : PT n m → ℂ)) y :=
    fun y ↦ (mulVec_single_apply' _ _ _).symm
  simp only [hT]
  unfold probA
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Tp_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Finset.sum_comm]
  by_cases hg : GoodZ (ampEstAmplitude A) m ((rr m c).val : ℤ)
  · rw [if_pos hg]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.sum_eq_single (rr m c)]
    · simp [hg]
    · intro o _ ho; simp [ho]
    · simp
  · rw [if_neg hg]
    refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun o _ ↦ ?_
    by_cases ho : o = rr m c
    · subst ho; simp [hg]
    · simp [ho]
open scoped Classical in
lemma good_of_pe {n : ℕ} (A : Unitary (2 ^ n)) (m : ℕ) (θ : ℝ)
    (ha : Real.sin (π * θ) ^ 2 = ampEstAmplitude A) (c : Fin (2 ^ (m + 3)))
    (h : IsPhaseEstimate (m + 3) θ (c.val : ℤ)) :
    GoodZ (ampEstAmplitude A) m ((rr m c).val : ℤ) := by
  have := trig_bound m _ θ ha c h
  unfold GoodZ
  show |_ - (((rv m c : ℕ) : ℤ) : ℝ) / _| ≤ _
  rw [Int.cast_natCast]
  exact this

open scoped Classical in
lemma probA_ge {n : ℕ} (A : Unitary (2 ^ n)) (m : ℕ) : 1 - 1 / (2 : ℝ) ^ 2 ≤ probA A m := by
  have h1 := succ_ge (m + 3) (phiA A / (2 * π))
  have h2 := succ_ge (m + 3) (-(phiA A / (2 * π)))
  have hs : (succM (m + 3) (phiA A / (2 * π)) + succM (m + 3) (-(phiA A / (2 * π)))) / 2 ≤
      probA A m := by
    unfold succM probA
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_le_sum fun c _ ↦ ?_
    have hw := wv_prob (m := m) A c
    have p1 := Complex.normSq_nonneg (Wm (m + 3) (phiA A / (2 * π)) c 0)
    have p2 := Complex.normSq_nonneg (Wm (m + 3) (-(phiA A / (2 * π))) c 0)
    by_cases hg : GoodZ (ampEstAmplitude A) m ((rr m c).val : ℤ)
    · rw [if_pos hg, hw]
      split_ifs <;> linarith
    · rw [if_neg hg]
      have n1 : ¬ IsPhaseEstimate (m + 3) (phiA A / (2 * π)) (c.val : ℤ) :=
        fun h ↦ hg (good_of_pe A m _ (sin_phiA A) c h)
      have n2 : ¬ IsPhaseEstimate (m + 3) (-(phiA A / (2 * π))) (c.val : ℤ) :=
        fun h ↦ hg (good_of_pe A m _ (sin_phiA_neg A) c h)
      rw [if_neg n1, if_neg n2]
      simp
  have e : (1 : ℝ) - 1 / 2 ^ 2 = 3 / 4 := by norm_num
  rw [e]
  linarith


/-! ## Stage 1: R runs side by side -/

section KronDefs

/-- Kronecker product of a family of matrices. -/
def kron {ι X : Type*} [Fintype ι] (A : ι → Matrix X X ℂ) : Matrix (ι → X) (ι → X) ℂ :=
  Matrix.of fun y x ↦ ∏ i, A i (y i) (x i)

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

end KronDefs

/-! ## The median (no choice at the data level) -/

open scoped Classical in
/-- The least value `v` such that more than half of the entries are at most `v`. -/
noncomputable def medN {R : ℕ} (y : Fin R → ℕ) : ℕ :=
  if h : ∃ v, R < 2 * (Finset.univ.filter fun i ↦ y i ≤ v).card then Nat.find h else 0

open scoped Classical in
lemma medN_lt {R N : ℕ} (hR : 0 < R) (y : Fin R → ℕ) (hy : ∀ i, y i < N) : medN y < N := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) (hy ⟨0, hR⟩)
  have hp : R < 2 * (Finset.univ.filter fun i ↦ y i ≤ N - 1).card := by
    have : (Finset.univ.filter fun i ↦ y i ≤ N - 1) = Finset.univ := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      have := hy i; omega
    rw [this, Finset.card_univ, Fintype.card_fin]; omega
  have h : ∃ v, R < 2 * (Finset.univ.filter fun i ↦ y i ≤ v).card := ⟨N - 1, hp⟩
  unfold medN
  rw [dif_pos h]
  exact lt_of_le_of_lt (Nat.find_min' h hp) (by omega)

open scoped Classical in
lemma medN_good {R : ℕ} (y : Fin R → ℕ) (G : ℕ → Prop)
    (hG : ∀ a b c, G a → G c → a ≤ b → b ≤ c → G b)
    (h : R < 2 * (Finset.univ.filter fun i ↦ G (y i)).card) : G (medN y) := by
  set S := Finset.univ.filter fun i ↦ G (y i) with hS
  have hne : S.Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image S y hne
  obtain ⟨i1, hi1, hmax⟩ := Finset.exists_max_image S y hne
  have hG0 : G (y i0) := (Finset.mem_filter.1 hi0).2
  have hG1 : G (y i1) := (Finset.mem_filter.1 hi1).2
  have hex : ∃ v, R < 2 * (Finset.univ.filter fun i ↦ y i ≤ v).card := by
    refine ⟨y i1, ?_⟩
    have hsub : S ⊆ Finset.univ.filter fun i ↦ y i ≤ y i1 := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hmax j hj
    have := Finset.card_le_card hsub
    omega
  have hmed : medN y = Nat.find hex := by
    unfold medN; rw [dif_pos hex]
  have hup : medN y ≤ y i1 := by
    rw [hmed]
    refine Nat.find_min' hex ?_
    have hsub : S ⊆ Finset.univ.filter fun i ↦ y i ≤ y i1 := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hmax j hj
    have := Finset.card_le_card hsub
    omega
  have hlo : y i0 ≤ medN y := by
    by_contra hlt
    push_neg at hlt
    have hspec := Nat.find_spec hex
    rw [← hmed] at hspec
    have hdisj : Disjoint (Finset.univ.filter fun i ↦ y i ≤ medN y) S := by
      rw [hS, Finset.disjoint_filter]
      intro j _ hj hGj
      have := hmin j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hGj⟩)
      omega
    have hc := Finset.card_union_of_disjoint hdisj
    have hle : ((Finset.univ.filter fun i ↦ y i ≤ medN y) ∪ S).card ≤ R := by
      calc _ ≤ (Finset.univ : Finset (Fin R)).card := Finset.card_le_card (Finset.subset_univ _)
        _ = R := by rw [Finset.card_univ, Fintype.card_fin]
    omega
  exact hG _ _ _ hG0 hG1 hlo hup

/-! ## Layout of the R runs -/

/-- The basis of the whole register: digit `0` is the output, digits `1..R` are the runs. -/
abbrev Yt (n m k : ℕ) := Fin (6 * (k + 1) + 1) → PT n m

/-- The median of the run values, as an element of the output register. -/
noncomputable def voteF (n m k : ℕ) (f : Fin (6 * (k + 1)) → PT n m) : Fin (2 ^ (m + 3)) :=
  ⟨medN (fun i ↦ (f i).1.1.val), medN_lt (by omega) _ fun i ↦ (f i).1.1.isLt⟩

/-- Add the median of the run values into the output digit. -/
noncomputable def shearEquiv (n m k : ℕ) : Equiv.Perm (Yt n m k) where
  toFun f := Function.update f 0
    (((f 0).1.1 + voteF n m k (fun i ↦ f i.succ), (f 0).1.2), (f 0).2)
  invFun f := Function.update f 0
    (((f 0).1.1 - voteF n m k (fun i ↦ f i.succ), (f 0).1.2), (f 0).2)
  left_inv f := by
    have hv : (fun i : Fin (6 * (k + 1)) ↦
        (Function.update f 0
          (((f 0).1.1 + voteF n m k (fun i ↦ f i.succ), (f 0).1.2), (f 0).2)) i.succ) =
        fun i ↦ f i.succ := by
      funext i
      exact Function.update_of_ne (Fin.succ_ne_zero i) _ _
    simp [hv]
  right_inv f := by
    have hv : (fun i : Fin (6 * (k + 1)) ↦
        (Function.update f 0
          (((f 0).1.1 - voteF n m k (fun i ↦ f i.succ), (f 0).1.2), (f 0).2)) i.succ) =
        fun i ↦ f i.succ := by
      funext i
      exact Function.update_of_ne (Fin.succ_ne_zero i) _ _
    simp [hv]

lemma shearEquiv_symm_apply (n m k : ℕ) (f : Yt n m k) :
    (shearEquiv n m k).symm f = Function.update f 0
      (((f 0).1.1 - voteF n m k (fun i ↦ f i.succ), (f 0).1.2), (f 0).2) := rfl

/-- The cost constant of the baseline. -/
def baselineRelCost : ℚ≥0 := 192

/-- Qubits: `R + 1` digits of `qq n m` wires. -/
def baselineQubits (n m k : ℕ) : ℕ := qq n m * (6 * (k + 1) + 1)

lemma card_Y (n m k : ℕ) : (2 ^ qq n m) ^ (6 * (k + 1) + 1) = 2 ^ baselineQubits n m k :=
  (pow_mul 2 (qq n m) (6 * (k + 1) + 1)).symm

noncomputable def eqv (n m k : ℕ) : Yt n m k ≃ Fin (2 ^ baselineQubits n m k) :=
  ((Equiv.refl (Fin (6 * (k + 1) + 1))).arrowCongr (eP n m)).trans
    (finFunctionFinEquiv.trans (finCongr (card_Y n m k)))

lemma digit_le (n m k : ℕ) (d : Fin (6 * (k + 1) + 1)) :
    qq n m * d.val + qq n m ≤ baselineQubits n m k := by
  unfold baselineQubits
  have := d.isLt
  calc qq n m * d.val + qq n m = qq n m * (d.val + 1) := by ring
    _ ≤ qq n m * (6 * (k + 1) + 1) := Nat.mul_le_mul_left _ (by omega)

/-- The wires of digit `d`. -/
noncomputable def regDig (n m k : ℕ) (d : Fin (6 * (k + 1) + 1)) :
    QRegister (qq n m) (baselineQubits n m k) :=
  QRegister.block (qq n m * d.val) (qq n m) (digit_le n m k d)

/-- The oracle register of run `i` (digit `i + 1`). -/
noncomputable def regD (n m k : ℕ) (i : Fin (6 * (k + 1))) :
    QRegister (n + 1) (baselineQubits n m k) :=
  (regDig n m k i.succ).compose (regO n m)

/-- The output register: the output part of digit `0`. -/
noncomputable def outReg (n m k : ℕ) : QRegister (m + 3) (baselineQubits n m k) :=
  (regDig n m k 0).compose (regR n m)

/-! ## Matrices on `Yt` -/

/-- `M` on digit `d`, identity elsewhere. -/
noncomputable def dgM (n m k : ℕ) (d : Fin (6 * (k + 1) + 1)) (M : Matrix (PT n m) (PT n m) ℂ) :
    Matrix (Yt n m k) (Yt n m k) ℂ :=
  kron fun i ↦ if i = d then M else 1

/-- `M` on every run digit, identity on the output digit. -/
noncomputable def runsM (n m k : ℕ) (M : Matrix (PT n m) (PT n m) ℂ) :
    Matrix (Yt n m k) (Yt n m k) ℂ :=
  kron fun i ↦ if i = 0 then 1 else M

lemma dgM_unit (n m k : ℕ) (d : Fin (6 * (k + 1) + 1)) (M : Matrix (PT n m) (PT n m) ℂ)
    (h : star M * M = 1) : star (dgM n m k d M) * dgM n m k d M = 1 :=
  kron_unitary _ fun i ↦ by by_cases hi : i = d <;> simp [hi, h]

lemma runsM_unit (n m k : ℕ) (M : Matrix (PT n m) (PT n m) ℂ)
    (h : star M * M = 1) : star (runsM n m k M) * runsM n m k M = 1 :=
  kron_unitary _ fun i ↦ by by_cases hi : i = 0 <;> simp [hi, h]

lemma qf_unit (m : ℕ) : star (qf m) * qf m = 1 := by
  have := Matrix.mem_unitaryGroup_iff'.1 (qftU (m + 3)).2
  rwa [qftU_val] at this

lemma qf_unit' (m : ℕ) : qf m * star (qf m) = 1 := by
  have := Matrix.mem_unitaryGroup_iff.1 (qftU (m + 3)).2
  rwa [qftU_val] at this

lemma kFi_unit (n m : ℕ) : star (kF n m (star (qf m))) * kF n m (star (qf m)) = 1 :=
  kF_unitary n m _ (by rw [star_star]; exact qf_unit' m)

lemma kFq_unit (n m : ℕ) : star (kF n m (qf m)) * kF n m (qf m) = 1 :=
  kF_unitary n m _ (qf_unit m)

/-- Fourier transform on every run's counting register. -/
noncomputable def stepAm (n m k : ℕ) : Matrix (Yt n m k) (Yt n m k) ℂ :=
  runsM n m k (kF n m (qf m))

/-- Inverse Fourier transform and rounding on every run, then the median into the output. -/
noncomputable def stepBm (n m k : ℕ) : Matrix (Yt n m k) (Yt n m k) ℂ :=
  permMat (shearEquiv n m k) *
    runsM n m k (permMat (shiftP n m) * kF n m (star (qf m)))

lemma stepAm_unit (n m k : ℕ) : star (stepAm n m k) * stepAm n m k = 1 :=
  runsM_unit n m k _ (kFq_unit n m)

lemma stepBm_unit (n m k : ℕ) : star (stepBm n m k) * stepBm n m k = 1 :=
  mul_unitary _ _ (permMat_unitary _)
    (runsM_unit n m k _ (mul_unitary _ _ (permMat_unitary _) (kFi_unit n m)))

/-! ## Atoms: steps and oracle calls -/

/-- A step is a unitary matrix on `Yt`; an oracle call is on the oracle register of one run. -/
inductive Atom (n m k : ℕ) where
  | st (M : Matrix (Yt n m k) (Yt n m k) ℂ) (h : star M * M = 1) : Atom n m k
  | ora (i : Fin (6 * (k + 1))) : Atom n m k

/-- A unitary on the `Yt` basis, as a unitary on the qubits. -/
noncomputable def luY (n m k : ℕ) (M : Matrix (Yt n m k) (Yt n m k) ℂ) (h : star M * M = 1) :
    Unitary (2 ^ baselineQubits n m k) :=
  ⟨liftMat (eqv n m k) M, Matrix.mem_unitaryGroup_iff'.2 (liftMat_star_mul _ _ h)⟩

noncomputable def Atom.circ {n m k : ℕ} :
    Atom n m k → OracleDynamicCircuit (Unitary (2 ^ baselineQubits n m k)) Var
      (baselineQubits n m k) (n + 1)
  | .st M h => .step (luY n m k M h)
  | .ora i => .oracle (regD n m k i)

noncomputable def Atom.unit {n m k : ℕ} (A : Unitary (2 ^ n)) :
    Atom n m k → Unitary (2 ^ baselineQubits n m k)
  | .st M h => luY n m k M h
  | .ora i => (regD n m k i).embedUnitary (ampEstOracle A)

noncomputable def Atom.mat {n m k : ℕ} (A : Unitary (2 ^ n)) :
    Atom n m k → Matrix (Yt n m k) (Yt n m k) ℂ
  | .st M _ => M
  | .ora i => dgM n m k i.succ (oraP A m)

noncomputable def circOf {n m k : ℕ} : List (Atom n m k) →
    OracleDynamicCircuit (Unitary (2 ^ baselineQubits n m k)) Var (baselineQubits n m k) (n + 1)
  | [] => .skip
  | a :: l => .seq a.circ (circOf l)

noncomputable def progOf {n m k : ℕ} (A : Unitary (2 ^ n)) :
    List (Atom n m k) → QProg Var (2 ^ baselineQubits n m k)
  | [] => QProg.skip
  | a :: l => QProg.qSeq (QProg.qAssign (a.unit A)) (progOf A l)

lemma compile_circOf {n m k : ℕ} (A : Unitary (2 ^ n)) (l : List (Atom n m k)) :
    (circOf l).compile QProg.qAssign (ampEstOracle A) = progOf A l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show QProg.qSeq _ _ = _
    rw [ih]
    cases a <;> rfl

/-- The atoms of one block of the Grover iterate in run `i`. -/
noncomputable def blockAtoms (n m k : ℕ) (i : Fin (6 * (k + 1))) (j : Fin (m + 3)) :
    List (Atom n m k) :=
  [.st (dgM n m k i.succ (aM n m j)) (dgM_unit n m k _ _ (aM_unitary n m j)), .ora i,
   .st (dgM n m k i.succ (bM n m j)) (dgM_unit n m k _ _ (bM_unitary n m j)), .ora i]

/-- All atoms of run `i` after the first Fourier transform. -/
noncomputable def runAtoms (n m k : ℕ) (i : Fin (6 * (k + 1))) : List (Atom n m k) :=
  .ora i :: (oracleCalls (m + 3)).flatMap (blockAtoms n m k i)

noncomputable def allAtoms (n m k : ℕ) : List (Atom n m k) :=
  .st (stepAm n m k) (stepAm_unit n m k) ::
    ((List.finRange (6 * (k + 1))).flatMap (runAtoms n m k) ++
      [.st (stepBm n m k) (stepBm_unit n m k)])

/-- The circuit of the baseline. -/
noncomputable def baselineCircuit (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ baselineQubits n m k)) Var (baselineQubits n m k) (n + 1) :=
  .seq (circOf (allAtoms n m k)) (.measure res (outReg n m k))

lemma compile_eq {n : ℕ} (A : Unitary (2 ^ n)) (m k : ℕ) :
    (baselineCircuit n m k).compile QProg.qAssign (ampEstOracle A) =
      QProg.qSeq (progOf A (allAtoms n m k)) (QProg.measureRegister res (outReg n m k)) := by
  simp only [baselineCircuit, OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_measure,
    compile_circOf]

/-! ## Tail bound -/

section Tail

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem prod_sum_weight (R : ℕ) (p w : X → ℝ) :
    ∑ y : Fin R → X, ∏ i, (p (y i) * w (y i)) = (∑ x, p x * w x) ^ R := by
  have h := Finset.prod_univ_sum (fun _ : Fin R ↦ (Finset.univ : Finset X))
    (fun _ x ↦ p x * w x)
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  simp

theorem total_prob (R : ℕ) (p : X → ℝ) (hsum : ∑ x, p x = 1) :
    ∑ y : Fin R → X, ∏ i, p (y i) = 1 := by
  have h := prod_sum_weight R p (fun _ ↦ 1)
  simp only [mul_one, hsum, one_pow] at h
  exact h

theorem tail_bound (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (good : X → Prop) [DecidablePred good]
    (hbad : ∑ x, (if good x then 0 else p x) ≤ 1 / 4) (R s : ℕ) (hR : R = 2 * s) :
    ∑ y : Fin R → X, (∏ i, p (y i)) *
      (if 2 * (Finset.univ.filter fun i ↦ good (y i)).card ≤ R then 1 else 0) ≤ (3 / 4) ^ s := by
  set w : X → ℝ := fun x ↦ if good x then 1 else 3 with hw
  have h3 : (0 : ℝ) < 3 ^ s := by positivity
  have hpt : ∀ y : Fin R → X, (∏ i, p (y i)) *
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
  calc _ ≤ ∑ y : Fin R → X, (∏ i, (p (y i) * w (y i))) / 3 ^ s :=
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

end Tail

lemma goodZ_convex (a : ℝ) (m : ℕ) :
    ∀ u b c : ℕ, GoodZ a m (u : ℤ) → GoodZ a m (c : ℤ) → u ≤ b → b ≤ c →
      GoodZ a m (b : ℤ) := by
  intro u b c hu hc hub hbc
  unfold GoodZ at *
  simp only [Int.cast_natCast] at *
  have hP : (0 : ℝ) < 2 ^ m := by positivity
  rw [abs_le] at *
  have h1 : (u : ℝ) / 2 ^ m ≤ b / 2 ^ m := by gcongr
  have h2 : (b : ℝ) / 2 ^ m ≤ c / 2 ^ m := by gcongr
  constructor <;> linarith [hu.1, hu.2, hc.1, hc.2]

open scoped Classical in
theorem success_gen (n m k : ℕ) (a : ℝ) (p : PT n m → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hsum : ∑ x, p x = 1)
    (hgood : 3 / 4 ≤ ∑ x, (if GoodZ a m (x.1.1.val : ℤ) then p x else 0)) :
    1 - 1 / (2 : ℝ) ^ k ≤ ∑ y : Fin (6 * (k + 1)) → PT n m, (∏ i, p (y i)) *
      (if GoodZ a m ((voteF n m k y).val : ℤ) then 1 else 0) := by
  have hbad : ∑ x, (if GoodZ a m (x.1.1.val : ℤ) then 0 else p x) ≤ 1 / 4 := by
    have : ∀ x : PT n m, (if GoodZ a m (x.1.1.val : ℤ) then 0 else p x) =
        p x - (if GoodZ a m (x.1.1.val : ℤ) then p x else 0) := by
      intro x; split_ifs <;> ring
    simp only [this, Finset.sum_sub_distrib, hsum]
    linarith
  have ht := tail_bound p hp hsum (fun x ↦ GoodZ a m (x.1.1.val : ℤ)) hbad
    (6 * (k + 1)) (3 * (k + 1)) (by ring)
  have htot := total_prob (6 * (k + 1)) p hsum
  have hs : (3 / 4 : ℝ) ^ (3 * (k + 1)) ≤ 1 / 2 ^ k := by
    have h1 : (3 / 4 : ℝ) ^ (3 * (k + 1)) = (27 / 64) ^ (k + 1) := by
      rw [pow_mul]; norm_num
    rw [h1, one_div, ← inv_pow]
    calc (27 / 64 : ℝ) ^ (k + 1) ≤ (2⁻¹) ^ (k + 1) := by gcongr; norm_num
      _ ≤ (2⁻¹) ^ k := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hpt : ∀ y : Fin (6 * (k + 1)) → PT n m, (∏ i, p (y i)) -
      (∏ i, p (y i)) * (if 2 * (Finset.univ.filter fun i ↦
        GoodZ a m ((y i).1.1.val : ℤ)).card ≤ 6 * (k + 1) then 1 else 0) ≤
      (∏ i, p (y i)) * (if GoodZ a m ((voteF n m k y).val : ℤ) then 1 else 0) := by
    intro y
    have hP0 : 0 ≤ ∏ i, p (y i) := Finset.prod_nonneg fun i _ ↦ hp _
    by_cases hif : 2 * (Finset.univ.filter fun i ↦
        GoodZ a m ((y i).1.1.val : ℤ)).card ≤ 6 * (k + 1)
    · rw [if_pos hif]; simp only [mul_one, sub_self]; positivity
    · rw [if_neg hif, mul_zero, sub_zero]
      have hlt : 6 * (k + 1) < 2 * (Finset.univ.filter fun i ↦
          GoodZ a m ((y i).1.1.val : ℤ)).card := not_le.1 hif
      have := medN_good (fun i ↦ (y i).1.1.val) (fun v ↦ GoodZ a m (v : ℤ))
        (goodZ_convex a m) (by convert hlt)
      have h' : GoodZ a m ((voteF n m k y).val : ℤ) := this
      rw [if_pos h', mul_one]
  have hsum2 := Finset.sum_le_sum fun y (_ : y ∈ (Finset.univ : Finset (Fin (6 * (k + 1)) → PT n m))) ↦ hpt y
  rw [Finset.sum_sub_distrib, htot] at hsum2
  linarith

/-! ## Stage 4a: embedding one digit -/

lemma testBit_digit (z i t D : ℕ) (ht : t < D) :
    (z / 2 ^ (D * i) % 2 ^ D).testBit t = z.testBit (D * i + t) := by
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [ht]
  rw [Nat.add_comm]

lemma bits_eq_iff {N : ℕ} (x y : Fin (2 ^ N)) (q : Fin N) :
    basisBits N x q = basisBits N y q ↔ x.val.testBit q.val = y.val.testBit q.val := by
  rw [basisBits_eq_div_mod, basisBits_eq_div_mod, ZMod.natCast_eq_natCast_iff', Nat.mod_mod,
    Nat.mod_mod, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
    decide_eq_decide]
  have := Nat.mod_lt (x.val / 2 ^ q.val) (show 0 < 2 by norm_num)
  have := Nat.mod_lt (y.val / 2 ^ q.val) (show 0 < 2 by norm_num)
  omega

lemma env_dig {D L : ℕ} (d : Fin L) (h : D * d.val + D ≤ D * L) (x y : Fin (2 ^ (D * L))) :
    ((QRegister.block (D * d.val) D h).basisSplitEquiv x).2 =
      ((QRegister.block (D * d.val) D h).basisSplitEquiv y).2 ↔
    ∀ i : Fin L, i ≠ d →
      x.val / 2 ^ (D * i.val) % 2 ^ D = y.val / 2 ^ (D * i.val) % 2 ^ D := by
  rw [QRegister.basisSplit_environment_eq_iff]
  constructor
  · intro hxy i hi
    apply Nat.eq_of_testBit_eq
    intro t
    by_cases ht : t < D
    · rw [testBit_digit _ _ _ _ ht, testBit_digit _ _ _ _ ht]
      have hq : D * i.val + t < D * L := by
        have := i.isLt
        calc D * i.val + t < D * i.val + D := by omega
          _ = D * (i.val + 1) := by ring
          _ ≤ D * L := Nat.mul_le_mul_left _ this
      have hnot : (⟨D * i.val + t, hq⟩ : Fin (D * L)) ∉
          Set.range (QRegister.block (D * d.val) D h).wires := by
        rintro ⟨j, hj⟩
        have h3 : D * d.val + j.val = D * i.val + t := congrArg Fin.val hj
        have hj2 := j.isLt
        apply hi
        have e1 : (D * d.val + j.val) / D = d.val := by
          rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj2, add_zero]
        have e2 : (D * i.val + t) / D = i.val := by
          rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt ht, add_zero]
        rw [h3] at e1
        exact Fin.ext (e2.symm.trans e1)
      exact (bits_eq_iff x y ⟨_, hq⟩).1 (hxy _ hnot)
    · simp [Nat.testBit_mod_two_pow, ht]
  · intro hxy q hq
    have hD : 0 < D := by
      have := q.isLt
      rcases Nat.eq_zero_or_pos D with h0 | h0
      · subst h0; simp at this
      · exact h0
    obtain ⟨i, hiL, t, htD, hqe⟩ : ∃ i, i < L ∧ ∃ t, t < D ∧ D * i + t = q.val :=
      ⟨q.val / D, Nat.div_lt_of_lt_mul q.isLt, q.val % D, Nat.mod_lt _ hD, Nat.div_add_mod _ _⟩
    have hne : (⟨i, hiL⟩ : Fin L) ≠ d := by
      intro hid
      apply hq
      refine ⟨⟨t, htD⟩, Fin.ext ?_⟩
      show D * d.val + t = q.val
      have : i = d.val := congrArg Fin.val hid
      rw [← this]; exact hqe
    rw [bits_eq_iff]
    have h2 := congrArg (fun z ↦ z.testBit t) (hxy ⟨i, hiL⟩ hne)
    simp only [testBit_digit _ _ _ _ htD, hqe] at h2
    exact h2

lemma env_regDig (n m k : ℕ) (d : Fin (6 * (k + 1) + 1)) (x y : Fin (2 ^ baselineQubits n m k)) :
    ((regDig n m k d).basisSplitEquiv x).2 = ((regDig n m k d).basisSplitEquiv y).2 ↔
      ∀ i : Fin (6 * (k + 1) + 1), i ≠ d →
        x.val / 2 ^ (qq n m * i.val) % 2 ^ qq n m = y.val / 2 ^ (qq n m * i.val) % 2 ^ qq n m :=
  env_dig d (digit_le n m k d) x y

lemma eqv_symm_val (n m k : ℕ) (g : Fin (2 ^ baselineQubits n m k))
    (i : Fin (6 * (k + 1) + 1)) :
    (eP n m ((eqv n m k).symm g i)).val = g.val / (2 ^ qq n m) ^ i.val % 2 ^ qq n m := by
  have : eP n m ((eqv n m k).symm g i) =
      finFunctionFinEquiv.symm ((finCongr (card_Y n m k)).symm g) i := by
    simp [eqv]
  rw [this, finFunctionFinEquiv_symm_apply_val]
  rfl

lemma eqv_symm_zero (n m k : ℕ) : (eqv n m k).symm 0 = fun _ ↦ ((0, 0), (0, 0)) := by
  funext i
  apply (eP n m).injective
  rw [eP_zero]
  apply Fin.ext
  rw [eqv_symm_val]
  simp

lemma extract_dig (n m k : ℕ) (d : Fin (6 * (k + 1) + 1)) (g : Fin (2 ^ baselineQubits n m k)) :
    (((regDig n m k d).extractIndex g : Fin (2 ^ qq n m)) : ℕ) =
      g.val / (2 ^ qq n m) ^ d.val % 2 ^ qq n m := by
  unfold regDig
  rw [extract_gen, pow_mul]

lemma embed_digit (n m k : ℕ) (d : Fin (6 * (k + 1) + 1)) (M : Matrix (PT n m) (PT n m) ℂ) :
    (regDig n m k d).embedMatrix (liftMat (eP n m) M) =
      liftMat (eqv n m k) (dgM n m k d M) := by
  ext g g'
  rw [QRegister.embedMatrix_apply]
  have e1 : ∀ z : Fin (2 ^ baselineQubits n m k),
      (regDig n m k d).extractIndex z = eP n m ((eqv n m k).symm z d) := by
    intro z
    apply Fin.ext
    rw [extract_dig, eqv_symm_val]
  rw [e1 g, e1 g', liftMat_apply]
  have hiff : ((regDig n m k d).basisSplitEquiv g).2 = ((regDig n m k d).basisSplitEquiv g').2 ↔
      ∀ i, i ≠ d → (eqv n m k).symm g i = (eqv n m k).symm g' i := by
    rw [env_regDig]
    simp only [pow_mul]
    refine forall_congr' fun i ↦ imp_congr_right fun _ ↦ ?_
    rw [← eqv_symm_val n m k g i, ← eqv_symm_val n m k g' i]
    exact ⟨fun h ↦ (eP n m).injective (Fin.ext h), fun h ↦ by rw [h]⟩
  show _ * _ = dgM n m k d M ((eqv n m k).symm g) ((eqv n m k).symm g')
  unfold dgM kron
  simp only [Matrix.of_apply]
  by_cases hE : ∀ i, i ≠ d → (eqv n m k).symm g i = (eqv n m k).symm g' i
  · rw [if_pos (hiff.2 hE), mul_one]
    rw [Finset.prod_eq_single d]
    · simp
    · intro i _ hi
      rw [if_neg hi, hE i hi]
      simp
    · simp
  · rw [if_neg (fun h ↦ hE (hiff.1 h)), mul_zero]
    push_neg at hE
    obtain ⟨i, hi, hne⟩ := hE
    symm
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [if_neg hi]
    exact Matrix.one_apply_ne hne

lemma oraEmb_val {n : ℕ} (A : Unitary (2 ^ n)) (m : ℕ) :
    ((regO n m).embedUnitary (ampEstOracle A)).1 = liftMat (eP n m) (oraP A m) := by
  rw [QRegister.embedUnitary_val]
  exact embed_eq A m

lemma Atom.unit_val {n m k : ℕ} (A : Unitary (2 ^ n)) (a : Atom n m k) :
    (a.unit A).1 = liftMat (eqv n m k) (a.mat A) := by
  cases a with
  | st M h => rfl
  | ora i =>
    show ((regD n m k i).embedUnitary (ampEstOracle A)).1 = _
    unfold regD
    rw [QRegister.embedUnitary_compose, QRegister.embedUnitary_val, oraEmb_val]
    exact embed_digit n m k i.succ _

/-! ## Stage 4b: the matrix of the whole program -/

lemma dgM_mul (n m k : ℕ) (d : Fin (6 * (k + 1) + 1)) (M N : Matrix (PT n m) (PT n m) ℂ) :
    dgM n m k d M * dgM n m k d N = dgM n m k d (M * N) := by
  unfold dgM
  rw [kron_mul]
  congr 1
  funext i
  by_cases hi : i = d <;> simp [hi]

lemma dgM_one (n m k : ℕ) (d : Fin (6 * (k + 1) + 1)) :
    dgM n m k d (1 : Matrix (PT n m) (PT n m) ℂ) = 1 := by
  unfold dgM
  rw [← kron_one]
  congr 1
  funext i
  by_cases hi : i = d <;> simp [hi]

lemma runsM_mul (n m k : ℕ) (M N : Matrix (PT n m) (PT n m) ℂ) :
    runsM n m k M * runsM n m k N = runsM n m k (M * N) := by
  unfold runsM
  rw [kron_mul]
  congr 1
  funext i
  by_cases hi : i = 0 <;> simp [hi]

/-- The matrix of a list of atoms. -/
noncomputable def prodMat {n m k : ℕ} (A : Unitary (2 ^ n)) :
    List (Atom n m k) → Matrix (Yt n m k) (Yt n m k) ℂ
  | [] => 1
  | a :: l => prodMat A l * a.mat A

lemma prodMat_append {n m k : ℕ} (A : Unitary (2 ^ n)) (l1 l2 : List (Atom n m k)) :
    prodMat A (l1 ++ l2) = prodMat A l2 * prodMat A l1 := by
  induction l1 with
  | nil => simp [prodMat]
  | cons a l ih =>
    simp only [List.cons_append, prodMat, ih, Matrix.mul_assoc]

lemma progOf_wp_mat {n m k : ℕ} (A : Unitary (2 ^ n)) (l : List (Atom n m k))
    (Θ : CQAssertion (Store Var) (2 ^ baselineQubits n m k)) (σ : Store Var) :
    ((wp (progOf A l) Θ) σ).1.mat =
      star (liftMat (eqv n m k) (prodMat A l)) * (Θ σ).1.mat *
        liftMat (eqv n m k) (prodMat A l) := by
  induction l with
  | nil => simp [progOf, prodMat, wp_skip, liftMat_one]
  | cons a l ih =>
    simp only [progOf, wp_qSeq, wp_qAssign]
    rw [CQAssertion.qAssign_apply_mat, ih, Atom.unit_val, prodMat, liftMat_mul]
    simp only [← Matrix.star_eq_conjTranspose, star_mul, Matrix.mul_assoc]

lemma prodMat_block {n m k : ℕ} (A : Unitary (2 ^ n)) (i : Fin (6 * (k + 1))) (j : Fin (m + 3)) :
    prodMat A (blockAtoms n m k i j) = dgM n m k i.succ (blkMat A m j) := by
  simp only [blockAtoms, prodMat, Atom.mat, Matrix.one_mul, blkMat, ← dgM_mul]

lemma prodMat_calls {n m k : ℕ} (A : Unitary (2 ^ n)) (i : Fin (6 * (k + 1)))
    (l : List (Fin (m + 3))) :
    prodMat A (l.flatMap (blockAtoms n m k i)) = dgM n m k i.succ (callsP A m l) := by
  induction l with
  | nil => simp [prodMat, callsP, dgM_one]
  | cons j l ih =>
    rw [List.flatMap_cons, prodMat_append, ih, prodMat_block, dgM_mul, callsP]

lemma prodMat_run {n m k : ℕ} (A : Unitary (2 ^ n)) (i : Fin (6 * (k + 1))) :
    prodMat A (runAtoms n m k i) =
      dgM n m k i.succ (callsP A m (oracleCalls (m + 3)) * oraP A m) := by
  unfold runAtoms
  simp only [prodMat, Atom.mat, prodMat_calls, dgM_mul]

lemma prodMat_runs {n m k : ℕ} (A : Unitary (2 ^ n)) :
    ∀ l : List (Fin (6 * (k + 1))), l.Nodup →
      prodMat A (l.flatMap (runAtoms n m k)) =
        kron (fun d : Fin (6 * (k + 1) + 1) ↦
          if d ∈ l.map Fin.succ then callsP A m (oracleCalls (m + 3)) * oraP A m else 1)
  | [], _ => by simp [prodMat, kron_one]
  | i :: l, hl => by
    have hnd := List.nodup_cons.1 hl
    rw [List.flatMap_cons, prodMat_append, prodMat_runs A l hnd.2, prodMat_run]
    unfold dgM
    rw [kron_mul]
    congr 1
    funext d
    by_cases hd : d = i.succ
    · subst hd
      have : Fin.succ i ∉ l.map Fin.succ := by
        intro h
        obtain ⟨j, hj, hji⟩ := List.mem_map.1 h
        exact hnd.1 (Fin.succ_injective _ hji ▸ hj)
      simp [this]
    · by_cases hm : d ∈ l.map Fin.succ
      · simp [hd, hm]
      · simp [hd, hm]

lemma mem_finRange_succ (k : ℕ) (d : Fin (6 * (k + 1) + 1)) :
    d ∈ (List.finRange (6 * (k + 1))).map Fin.succ ↔ d ≠ 0 := by
  constructor
  · intro h
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 h
    exact Fin.succ_ne_zero j
  · intro hd
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hd
    exact List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩

lemma prodMat_all {n : ℕ} (A : Unitary (2 ^ n)) (m k : ℕ) :
    prodMat A (allAtoms n m k) =
      permMat (shearEquiv n m k) * runsM n m k (Tp A m) := by
  have hmid : prodMat A ((List.finRange (6 * (k + 1))).flatMap (runAtoms n m k)) =
      runsM n m k (callsP A m (oracleCalls (m + 3)) * oraP A m) := by
    rw [prodMat_runs A _ (List.nodup_finRange _)]
    unfold runsM
    congr 1
    funext d
    by_cases hd : d = 0 <;> simp [mem_finRange_succ, hd]
  unfold allAtoms
  simp only [prodMat, List.singleton_append, prodMat_append, Atom.mat, Matrix.one_mul, hmid]
  unfold stepBm stepAm
  simp only [Matrix.mul_assoc, runsM_mul]
  congr 2
  unfold Tp
  simp only [Matrix.mul_assoc]

/-- The map from the run outcomes to the final amplitude. -/
lemma Phi_apply {n : ℕ} (A : Unitary (2 ^ n)) (m k : ℕ) (f : Yt n m k) :
    (permMat (shearEquiv n m k) * runsM n m k (Tp A m)) f (fun _ ↦ ((0, 0), (0, 0))) =
      (if f 0 = ((voteF n m k (fun i ↦ f i.succ), 0), (0, 0)) then 1 else 0) *
        ∏ i : Fin (6 * (k + 1)), (Tp A m *ᵥ (Pi.single ((0, 0), (0, 0)) (1 : ℂ) : PT n m → ℂ))
          (f i.succ) := by
  rw [← mulVec_single_apply' (permMat (shearEquiv n m k) * runsM n m k (Tp A m))
    (fun _ ↦ ((0, 0), (0, 0))) f, single_zero_prod]
  unfold runsM
  rw [← Matrix.mulVec_mulVec, permMat_mulVec, kron_mulVec_prod]
  simp only []
  rw [Fin.prod_univ_succ (n := 6 * (k + 1))]
  have hs : ∀ j : Fin (6 * (k + 1)), (shearEquiv n m k).symm f j.succ = f j.succ := by
    intro j
    rw [shearEquiv_symm_apply]
    exact Function.update_of_ne (Fin.succ_ne_zero j) _ _
  have h0 : (shearEquiv n m k).symm f 0 =
      (((f 0).1.1 - voteF n m k (fun i ↦ f i.succ), (f 0).1.2), (f 0).2) := by
    rw [shearEquiv_symm_apply]
    simp
  simp only [hs, h0, if_true, Matrix.one_mulVec, Pi.single_apply]
  congr 1
  obtain ⟨⟨o, c⟩, ⟨a, s⟩⟩ := f 0
  simp [Prod.ext_iff, sub_eq_zero]

/-! ## Cost -/

lemma unitaryCost_le_one {n : ℕ} (A : Unitary (2 ^ n)) {q : ℕ} (U : Unitary (2 ^ q)) :
    (CostModel.ofEmbeddedOracle (n := q) (ampEstOracle A)).unitaryCost U ≤ 1 := by
  unfold CostModel.ofEmbeddedOracle
  dsimp only
  split_ifs <;> simp

lemma assign_cost {n : ℕ} (A : Unitary (2 ^ n)) {q : ℕ} (U : Unitary (2 ^ q)) :
    CostBound (CostModel.ofEmbeddedOracle (ampEstOracle A)) (QProg.qAssign U : QProg Var (2 ^ q))
      1 :=
  CostBound.mono (CostBound.qAssign _ U) (by exact_mod_cast unitaryCost_le_one A U)

lemma progOf_cost {n m k : ℕ} (A : Unitary (2 ^ n)) (l : List (Atom n m k)) :
    CostBound (CostModel.ofEmbeddedOracle (ampEstOracle A)) (progOf A l) (l.length : ℝ≥0) := by
  induction l with
  | nil => simpa [progOf] using CostBound.skip_zero (Var := Var) _
  | cons a l ih =>
    refine CostBound.mono (CostBound.seq (assign_cost A _) ih) (le_of_eq ?_)
    simp only [List.length_cons]
    push_cast
    ring

lemma length_flatMap_const {α β : Type*} (f : α → List β) (c : ℕ) :
    ∀ l : List α, (∀ a ∈ l, (f a).length = c) → (l.flatMap f).length = l.length * c
  | [], _ => by simp
  | a :: l, h => by
    rw [List.flatMap_cons, List.length_append, h a (by simp),
      length_flatMap_const f c l (fun b hb ↦ h b (by simp [hb]))]
    simp [Nat.succ_mul]; ring

lemma length_runAtoms (n m k : ℕ) (i : Fin (6 * (k + 1))) :
    (runAtoms n m k i).length = 1 + 4 * (oracleCalls (m + 3)).length := by
  unfold runAtoms
  rw [List.length_cons, length_flatMap_const _ 4 _ (fun j _ ↦ rfl)]
  ring

lemma length_allAtoms (n m k : ℕ) :
    (allAtoms n m k).length ≤ 192 * 2 ^ m * (k + 1) := by
  unfold allAtoms
  rw [List.length_cons, List.length_append, length_flatMap_const _ _ _
    (fun i _ ↦ length_runAtoms n m k i), List.length_finRange]
  have h := oracleCalls_length (m + 3)
  have h8 : 2 ^ (m + 3) = 8 * 2 ^ m := by rw [pow_add]; ring
  rw [h8] at h
  generalize (oracleCalls (m + 3)).length = L at h ⊢
  generalize 2 ^ m = P at h ⊢
  have h3 : 1 + 4 * L + 3 = 32 * P := by omega
  have h4 : (6 * (k + 1)) * (1 + 4 * L) + (6 * (k + 1)) * 3 = (6 * (k + 1)) * (32 * P) := by
    rw [← mul_add, h3]
  simp only [List.length_singleton]
  nlinarith

lemma baseline_cost {n : ℕ} (A : Unitary (2 ^ n)) (m k : ℕ) :
    CostBound (CostModel.ofEmbeddedOracle (ampEstOracle A))
      (qset ;; (baselineCircuit n m k).compile QProg.qAssign (ampEstOracle A))
      (((baselineRelCost : ℚ≥0) : ℝ≥0) * 2 ^ m * (k + 1)) := by
  rw [compile_eq]
  refine CostBound.mono (CostBound.seq (CostBound.qSet _) (CostBound.seq (progOf_cost A _)
    (CostBound.qMeasure _ _ _))) ?_
  have h192 : ((baselineRelCost : ℚ≥0) : ℝ≥0) = 192 := by
    unfold baselineRelCost; norm_num
  have hnat := length_allAtoms n m k
  have hcast : (((allAtoms n m k).length : ℕ) : ℝ≥0) ≤ 192 * 2 ^ m * (k + 1) := by
    exact_mod_cast hnat
  rw [h192]
  refine le_trans (le_of_eq ?_) hcast
  simp [CostModel.ofEmbeddedOracle]

/-! ## The triple -/

lemma extract_outReg (n m k : ℕ) (g : Fin (2 ^ baselineQubits n m k)) :
    (((outReg n m k).extractIndex g : Fin (2 ^ (m + 3))) : ℕ) =
      (((eqv n m k).symm g 0).1.1).val := by
  have e : (regDig n m k 0).extractIndex g = eP n m ((eqv n m k).symm g 0) := by
    apply Fin.ext
    rw [extract_dig, eqv_symm_val]
  unfold outReg
  rw [QRegister.extractIndex_compose, e]
  generalize (eqv n m k).symm g 0 = p
  obtain ⟨⟨o, c⟩, ⟨a, s⟩⟩ := p
  exact extractR m o c a s

lemma blkMat_unitary {n : ℕ} (A : Unitary (2 ^ n)) (m : ℕ) (j : Fin (m + 3)) :
    star (blkMat A m j) * blkMat A m j = 1 := by
  unfold blkMat
  exact mul_unitary _ _ (mul_unitary _ _ (mul_unitary _ _ (oraP_unitary A m) (bM_unitary n m j))
    (oraP_unitary A m)) (aM_unitary n m j)

lemma callsP_unitary {n : ℕ} (A : Unitary (2 ^ n)) (m : ℕ) (l : List (Fin (m + 3))) :
    star (callsP A m l) * callsP A m l = 1 := by
  induction l with
  | nil => simp [callsP]
  | cons j l ih => exact mul_unitary _ _ ih (blkMat_unitary A m j)

lemma Tp_unitary {n : ℕ} (A : Unitary (2 ^ n)) (m : ℕ) :
    star (Tp A m) * Tp A m = 1 := by
  unfold Tp
  exact mul_unitary _ _ (mul_unitary _ _ (mul_unitary _ _ (mul_unitary _ _
    (permMat_unitary _) (kFi_unit n m)) (callsP_unitary A m _)) (oraP_unitary A m))
    (kFq_unit n m)

open scoped Classical in
lemma sum_p_gen {n : ℕ} (A : Unitary (2 ^ n)) (m : ℕ) :
    ∑ x : PT n m, Complex.normSq (Tp A m x ((0, 0), (0, 0))) = 1 := by
  have h := entry_gen (Tp A m) (fun _ ↦ True) ((0, 0), (0, 0))
  simp only [if_true, Matrix.diagonal_one, Matrix.mul_one, Tp_unitary] at h
  have h2 : ((∑ x : PT n m, Complex.normSq (Tp A m x ((0, 0), (0, 0))) : ℝ) : ℂ) = 1 := by
    rw [← h]; simp
  exact_mod_cast h2

open scoped Classical in
/-- The success probability of the baseline. -/
noncomputable def probP {n : ℕ} (A : Unitary (2 ^ n)) (m k : ℕ) : ℝ :=
  ∑ y : Fin (6 * (k + 1)) → PT n m,
    (∏ i, Complex.normSq (Tp A m (y i) ((0, 0), (0, 0)))) *
      (if GoodZ (ampEstAmplitude A) m ((voteF n m k y).val : ℤ) then 1 else 0)

open scoped Classical in
lemma probP_ge {n : ℕ} (A : Unitary (2 ^ n)) (m k : ℕ) :
    1 - 1 / (2 : ℝ) ^ k ≤ probP A m k := by
  refine success_gen n m k (ampEstAmplitude A) (fun x ↦ Complex.normSq (Tp A m x ((0, 0), (0, 0))))
    (fun x ↦ Complex.normSq_nonneg _) (sum_p_gen A m) ?_
  have h := probA_ge A m
  rw [← sum_formula A m] at h
  norm_num at h ⊢
  linarith

open scoped Classical in
noncomputable def gF {n : ℕ} (A : Unitary (2 ^ n)) (m k : ℕ) (f : Yt n m k) : ℝ :=
  if GoodZ (ampEstAmplitude A) m ((f 0).1.1.val : ℤ) then
    Complex.normSq ((permMat (shearEquiv n m k) * runsM n m k (Tp A m)) f
      (fun _ ↦ ((0, 0), (0, 0)))) else 0

open scoped Classical in
lemma sum_formula_gen {n : ℕ} (A : Unitary (2 ^ n)) (m k : ℕ) :
    (∑ g : Fin (2 ^ baselineQubits n m k),
      if GoodZ (ampEstAmplitude A) m (((outReg n m k).extractIndex g).val : ℤ)
      then Complex.normSq ((liftMat (eqv n m k) (prodMat A (allAtoms n m k))) g 0) else 0) =
        probP A m k := by
  have h1 : ∀ g : Fin (2 ^ baselineQubits n m k),
      (if GoodZ (ampEstAmplitude A) m (((outReg n m k).extractIndex g).val : ℤ)
        then Complex.normSq ((liftMat (eqv n m k) (prodMat A (allAtoms n m k))) g 0) else 0) =
      gF A m k ((eqv n m k).symm g) := by
    intro g
    have e0 : (((outReg n m k).extractIndex g : Fin (2 ^ (m + 3))) : ℕ) =
        (((eqv n m k).symm g) 0).1.1.val := extract_outReg n m k g
    have e1 : (liftMat (eqv n m k) (prodMat A (allAtoms n m k))) g 0 =
        (permMat (shearEquiv n m k) * runsM n m k (Tp A m)) ((eqv n m k).symm g)
          (fun _ ↦ ((0, 0), (0, 0))) := by
      show prodMat A (allAtoms n m k) ((eqv n m k).symm g) ((eqv n m k).symm 0) = _
      rw [eqv_symm_zero, prodMat_all]
    rw [e0, e1]
    rfl
  calc _ = ∑ g : Fin (2 ^ baselineQubits n m k), gF A m k ((eqv n m k).symm g) :=
        Finset.sum_congr rfl fun g _ ↦ h1 g
    _ = ∑ f, gF A m k f := Equiv.sum_comp (eqv n m k).symm (gF A m k)
    _ = probP A m k := by
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (6 * (k + 1) + 1) ↦ PT n m)) (gF A m k),
        Fintype.sum_prod_type, Finset.sum_comm]
      unfold probP
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [Finset.sum_eq_single (((voteF n m k y), 0), ((0 : Fin (2 ^ n)), (0 : Fin 2)))]
      · simp only [gF, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ, Phi_apply]
        by_cases hp : GoodZ (ampEstAmplitude A) m ((voteF n m k y).val : ℤ)
        · simp [hp, map_prod, mulVec_single_apply']
        · simp [hp]
      · intro a _ ha
        simp [gF, Fin.consEquiv_apply, Phi_apply, ha]
      · simp

open scoped Classical in
lemma wp_mat {n : ℕ} (A : Unitary (2 ^ n)) (m k : ℕ) (σ : Store Var) :
    ((wp (qset ;; (baselineCircuit n m k).compile QProg.qAssign (ampEstOracle A))
      (fun σ ↦ ⌜GoodZ (ampEstAmplitude A) m (σ res)⌝)) σ).1.mat =
      ((probP A m k : ℝ) : ℂ) • (1 : Matrix (Fin (2 ^ baselineQubits n m k))
        (Fin (2 ^ baselineQubits n m k)) ℂ) := by
  rw [compile_eq]
  simp only [wp_qSeq, wp_qSet]
  rw [CQAssertion.qSet_apply_mat, progOf_wp_mat, meas_mat',
    entry_gen _ (fun g ↦ GoodZ (ampEstAmplitude A) m (((outReg n m k).extractIndex g).val : ℤ)) 0,
    sum_formula_gen]

lemma baseline_triple {n : ℕ} (A : Unitary (2 ^ n)) (m k : ℕ) :
    ⦃ CQAssertion.ofProb (1 - 1 / (2 : ℝ) ^ k) ⦄
      (qset ;; (baselineCircuit n m k).compile QProg.qAssign (ampEstOracle A))
      ⦃ fun σ ↦ ⌜|ampEstAmplitude A - (σ res : ℝ) / (2 : ℝ) ^ m| ≤ 1 / (2 : ℝ) ^ m⌝ ⦄ := by
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have hdiv : 1 / (2 : ℝ) ^ k ≤ 1 := by rw [div_le_one hpos]; exact h2k
  have hdiv0 : 0 ≤ 1 / (2 : ℝ) ^ k := by positivity
  show ⦃ CQAssertion.ofProb (1 - 1 / (2 : ℝ) ^ k) ⦄
      (qset ;; (baselineCircuit n m k).compile QProg.qAssign (ampEstOracle A))
      ⦃ fun σ ↦ ⌜GoodZ (ampEstAmplitude A) m (σ res)⌝ ⦄
  refine Triple.of_le_wp fun σ ↦ Subtype.coe_le_coe.mp ?_
  rw [CQAssertion.ofProb_apply_of_bounds _ (by linarith) (by linarith)]
  have h : ((wp (qset ;; (baselineCircuit n m k).compile QProg.qAssign (ampEstOracle A))
      (fun σ ↦ ⌜GoodZ (ampEstAmplitude A) m (σ res)⌝)) σ).1 =
      probP A m k • (1 : HermitianMat (Fin (2 ^ baselineQubits n m k)) ℂ) := by
    apply HermitianMat.ext
    rw [wp_mat, HermitianMat.mat_smul, HermitianMat.mat_one, Complex.coe_smul]
  rw [h]
  exact smul_le_smul_of_nonneg_right (probP_ge A m k) zero_le_one

/-! ## Main theorem -/

theorem ampEst_general_baseline :
    ∃ (c : ℚ≥0) (q : ℕ → ℕ → ℕ → ℕ)
      (C : ∀ n m k : ℕ, OracleDynamicCircuit (Unitary (2 ^ q n m k)) Var (q n m k) (n + 1)),
      ∀ (n m k : ℕ) (A : Unitary (2 ^ n)),
        (⦃ CQAssertion.ofProb (1 - 1 / (2 : ℝ) ^ k) ⦄
          (qset ;; (C n m k).compile QProg.qAssign (ampEstOracle A))
          ⦃ fun σ ↦ ⌜|ampEstAmplitude A - (σ res : ℝ) / (2 : ℝ) ^ m| ≤ 1 / (2 : ℝ) ^ m⌝ ⦄) ∧
        CostBound (CostModel.ofEmbeddedOracle (ampEstOracle A))
          (qset ;; (C n m k).compile QProg.qAssign (ampEstOracle A)) (c * 2 ^ m * (k + 1)) :=
  ⟨baselineRelCost, baselineQubits, baselineCircuit,
    fun n m k A ↦ ⟨baseline_triple A m k, baseline_cost A m k⟩⟩

/-- Wrapper with abbreviation reducibility hints. The Comparator compares `ampEstProgram`
including its reducibility height, which is computed from the definitions it mentions; the
abbreviation keeps the height of `ampEstCircuit` out of that computation, so it matches the
challenge's (where `ampEstCircuit` is a hole). It changes no meaning. -/
noncomputable abbrev circuitW (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ baselineQubits n m k)) Var (baselineQubits n m k) (n + 1) :=
  baselineCircuit n m k

end AmpEstBaselineGeneral

/-- Total number of qubits used by `ampEstCircuit`. -/
def ampEstQubits (n m k : ℕ) : ℕ := AmpEstBaselineGeneral.baselineQubits n m k

/-- Query-model circuit on `ampEstQubits n m k` qubits with `(n + 1)`-qubit select-oracle calls
that writes an `m`-bit estimate of the success probability into `res`. -/
noncomputable def ampEstCircuit (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ ampEstQubits n m k)) Var (ampEstQubits n m k) (n + 1) :=
  AmpEstBaselineGeneral.circuitW n m k

open QProg.Notation in
/-- Reset all qubits, then run `ampEstCircuit` compiled with `oracle`. -/
noncomputable def ampEstProgram (n m k : ℕ)
    (oracle : Unitary (2 ^ (n + 1))) : QProg Var (2 ^ ampEstQubits n m k) :=
  qset ;; (ampEstCircuit n m k).compile QProg.qAssign oracle

/-- `ampEstProgram n m k` writes into `res` an integer with
`|ampEstAmplitude A - res / 2 ^ m| ≤ 1 / 2 ^ m` with probability at least `1 - 1 / 2 ^ k`, for
every `n`, precision `m`, confidence parameter `k` and unitary `A`. -/
theorem ampEst_correctness (n m k : ℕ) (A : Unitary (2 ^ n)) :
    ⦃ CQAssertion.ofProb (1 - 1 / (2 : ℝ) ^ k) ⦄
    ampEstProgram n m k (ampEstOracle A)
    ⦃ fun σ ↦ ⌜|ampEstAmplitude A - (σ res : ℝ) / (2 : ℝ) ^ m| ≤ 1 / (2 : ℝ) ^ m⌝ ⦄ := by
  exact AmpEstBaselineGeneral.baseline_triple A m k

/-- Claimed constant in the expected oracle-call bound `ampEstRelCost * 2 ^ m * (k + 1)`. -/
def ampEstRelCost : ℚ≥0 := 192

/-- Expected oracle-call bound for `ampEstProgram n m k`, uniform in `n`, `m`, `k` and `A`. -/
theorem ampEst_rel_cost (n m k : ℕ) (A : Unitary (2 ^ n)) :
    CostBound (CostModel.ofEmbeddedOracle (ampEstOracle A))
      (ampEstProgram n m k (ampEstOracle A))
      (ampEstRelCost * 2 ^ m * (k + 1)) := by
  exact AmpEstBaselineGeneral.baseline_cost A m k

/-!
## Pinned instance

A single-number record at precision `m = 10` (additive error `1 / 1024`) and confidence `k = 10`
(failure probability at most `1 / 1024`): the expected number of oracle calls of
`ampEstProgram` at that size is bounded by a closed constant. A solution may treat the pinned
size separately from the general family.
-/

/-- Claimed expected oracle-call bound for `ampEstProgram` at `m = 10`, `k = 10`. -/
def ampEstM10K10ConstCost : ℚ≥0 := 2162688

/-- Expected oracle-call bound at the pinned size `m = 10`, `k = 10`, uniform in `n` and `A`. -/
theorem ampEst_m10_k10_const_cost (n : ℕ) (A : Unitary (2 ^ n)) :
    CostBound (CostModel.ofEmbeddedOracle (ampEstOracle A))
      (ampEstProgram n 10 10 (ampEstOracle A))
      ampEstM10K10ConstCost := by
  refine CostBound.mono (AmpEstBaselineGeneral.baseline_cost A 10 10) ?_
  unfold ampEstM10K10ConstCost AmpEstBaselineGeneral.baselineRelCost
  norm_num

end QuantumComputation.Specs
