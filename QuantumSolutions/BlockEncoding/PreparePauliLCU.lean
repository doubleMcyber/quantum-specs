/-
Copyright 2026 Marlon Moenius
Portions Copyright 2026 Google LLC (marked GOOGLE-DERIVED below)
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

public import QuantumComputation.Circuits.DynamicCircuit
public import QuantumComputation.Circuits.ResourceCounting
public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import QuantumComputation.Registers.Embed

/-!
# LCU `PREPARE` Specification

`PREPARE` is the state-preparation operation of a linear combination of unitaries (Childs and
Wiebe; Babbush et al., Section III.D). Given `b` index qubits, a number of terms `L` with
`1 ≤ L ≤ 2^b`, a precision `μ` (a number of bits), and classical rational weights
`w_0, …, w_{L-1} ≥ 0` with `λ = ∑_j w_j > 0`, the program must map the all-zero state of an index
register (`b` qubits) and a garbage register (`prepareGarbage b L μ` qubits) to a pure state
`∑_j a_j |j⟩|g_j⟩`, with unit garbage states `g_j`, whose index probabilities
`p_j = |a_j|^2` (the marginal distribution of the index register) satisfy
* `p_j = 0` for every index value `j ≥ L`, and
* `|p_j - w_j / λ| ≤ 1 / (2^μ L)` for every `j < L`.

The phases of the `a_j` and the garbage states are free: in `⟨PREP| SELECT |PREP⟩` they cancel
when `SELECT` is diagonal in the index and does not touch the garbage, so garbage entangled with
the index is allowed, as in coherent alias sampling. Clean ancillas
(`prepareAncillas b L μ` qubits) start in `|0⟩` and must be returned to `|0⟩`. The program must
act as one unitary on every input of index plus garbage, so that its inverse exists for the
reflection of a qubitized walk; only the image of the all-zero input is tied to the weights. A global
phase of the whole program is not observable and is not constrained.

Formally, there must exist a unitary `W` on index plus garbage whose column `W |0⟩` has these
index probabilities (`PrepareApproximates`), and the program must realize `W` on index plus
garbage with clean ancillas, for every input state of index plus garbage
(`RealizesCleanSubroutine`). The output from the all-zero input is then the pure state
`W |0⟩ ⊗ |0⟩`, so a program that measures the index and leaves a classical mixture, or one that
resets its registers before preparing, does not satisfy
it. The weights are classical data known when the circuit is built, so the program may depend on
them arbitrarily. The statement holds for all `b`, `L`, `μ` and all weight tables.

Encoding (the library's little-endian convention, `basisBits`): the program acts on a data
register `rData` of `b + prepareGarbage b L μ` wires followed by the ancilla register. Logical
wires `0, …, b - 1` of `rData` are the index register, wire `i` carrying bit `i` of `j` (least
significant first); the remaining wires are the garbage register. The data basis index of index
value `j` and garbage basis index `x` is `j + 2^b * x` (`prepareDataEquiv`).
In a qubitized walk the registers compose as system, then index, then garbage: the `SELECT`
specification acts on system and index (system first), this one on index and garbage.

Cost: two theorems, both over Clifford + `T` with measurements, both excluding primitive `TOFF`
gates (so each Toffoli is costed by its Clifford + `T` construction, such as `4` `T` gates with an
ancilla and a measurement), and both holding for every weight table with `w_j ≥ 0` and `λ > 0` and
every register placement. `prepare_t_cost` bounds the `T` count by the claimed
`prepareTCost b L μ` for all `b`, `1 ≤ L ≤ 2^b` and `μ`, as in the THC specification.
`prepare_b4mu8_spacetime_cost` bounds `T count * qubits` by the closed constant
`prepareB4Mu8SpacetimeCost` at the pinned size `b = 4`, `L = 16`, `μ = 8`
(`PrepareSize.b4mu8`), as in Google's arcsine specification at `k25`, where
`qubits = b + prepareGarbage b L μ + prepareAncillas b L μ` counts all index, garbage and clean
ancilla qubits. The garbage width, the ancilla count and `prepareTCost` depend only on
`(b, L, μ)`, never on the weights.

References: R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler,
H. Neven, "Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity",
Phys. Rev. X 8, 041015 (2018), arXiv:1805.03662 (Section III.D: coherent alias sampling with
`μ`-bit keep values prepares probabilities within `1 / (2^μ L)` of `w_ℓ / λ`, with a `T` count of
`4 (L + μ) + O(log L)`); A. M. Childs and N. Wiebe, arXiv:1202.5822 (linear combination of
unitaries); G. H. Low and I. L. Chuang, arXiv:1610.06546 (qubitization).
-/

@[expose] public section


namespace QuantumComputation.Specs

open Operator Matrix

/-!
## Weights, Index Probabilities and the Target Property
-/

/-- Classical table of `L` rational weights `w_0, …, w_{L-1}`. The correctness and cost theorems
assume `0 ≤ w_j` for all `j` and `0 < prepareLambda w`. -/
abbrev PrepareWeights (L : ℕ) : Type := Fin L → ℚ

/-- The `1`-norm `λ = ∑_j w_j` of a weight table. -/
def prepareLambda {L : ℕ} (w : PrepareWeights L) : ℚ :=
  ∑ j, w j

/-- Data basis index of index value `j` and garbage basis index `x`: `(j, x) ↦ j + 2^b * x`, so
the index register occupies the `b` least significant bits (the first `b` data wires). -/
def prepareDataEquiv (b g : ℕ) : Fin (2 ^ b) × Fin (2 ^ g) ≃ Fin (2 ^ (b + g)) :=
  (Equiv.prodComm _ _).trans (finProdFinEquiv.trans (finCongr (by rw [pow_add, mul_comm])))

theorem prepareDataEquiv_val (b g : ℕ) (j : Fin (2 ^ b)) (x : Fin (2 ^ g)) :
    (prepareDataEquiv b g (j, x)).val = j.val + 2 ^ b * x.val := rfl

/-- Marginal probability `p_j = ∑_x |ψ_{j, x}|^2` of index value `j` in a state `ψ` of index
(`b` qubits) plus garbage (`g` qubits). Writing `ψ = ∑_j a_j |j⟩|g_j⟩` with unit `g_j`, this is
`|a_j|^2`. -/
noncomputable def prepareIndexProb (b g : ℕ) (ψ : Fin (2 ^ (b + g)) → ℂ) (j : Fin (2 ^ b)) :
    ℝ :=
  ∑ x : Fin (2 ^ g), ‖ψ (prepareDataEquiv b g (j, x))‖ ^ 2

/-- The state `ψ` of index plus garbage prepares the weights `w` to `μ` bits: index values
`j ≥ L` have probability `0`, and every `j < L` has probability within `1 / (2^μ L)` of
`w_j / λ`. -/
def PrepareApproximates (b g L μ : ℕ) (w : PrepareWeights L) (ψ : Fin (2 ^ (b + g)) → ℂ) :
    Prop :=
  (∀ j : Fin (2 ^ b), L ≤ j.val → prepareIndexProb b g ψ j = 0) ∧
    ∀ (j : Fin (2 ^ b)) (hj : j.val < L),
      |prepareIndexProb b g ψ j - ((w ⟨j.val, hj⟩ / prepareLambda w : ℚ) : ℝ)| ≤
        1 / (2 ^ μ * L)

/-!
## Sanity Checks
-/

/-- The all-zero data state is the basis state with index `0` and garbage `0`. -/
theorem prepareDataEquiv_zero (b g : ℕ) : prepareDataEquiv b g (0, 0) = 0 :=
  Fin.ext (by simp [prepareDataEquiv_val])

/-- A basis state with index value `j₀` gives index probability `1` at `j₀` and `0` elsewhere. -/
theorem prepareIndexProb_basisState (b g : ℕ) (j₀ : Fin (2 ^ b)) (x₀ : Fin (2 ^ g))
    (j : Fin (2 ^ b)) :
    prepareIndexProb b g (basisState (prepareDataEquiv b g (j₀, x₀))) j =
      if j = j₀ then 1 else 0 := by
  unfold prepareIndexProb
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single x₀]
    · simp [basisState]
    · intro x _ hx
      simp [basisState, hx]
    · intro hx
      exact absurd (Finset.mem_univ x₀) hx
  · refine Finset.sum_eq_zero fun x _ ↦ ?_
    simp [basisState, h]

/-- Satisfiable: with `b = 0`, `L = 1` and no garbage, the identity unitary prepares every valid
one-term weight table exactly, at every precision `μ`. -/
theorem prepareApproximates_one_trivial (μ : ℕ) (w : PrepareWeights 1)
    (hsum : 0 < prepareLambda w) :
    PrepareApproximates 0 0 1 μ w ((1 : Unitary (2 ^ (0 + 0))).1 *ᵥ basisState 0) := by
  have hψ : (1 : Unitary (2 ^ (0 + 0))).1 *ᵥ basisState 0 =
      basisState (prepareDataEquiv 0 0 (0, 0)) := by
    rw [prepareDataEquiv_zero]
    exact Matrix.one_mulVec _
  have hlam : prepareLambda w = w 0 := by
    simp [prepareLambda]
  have hw0 : w 0 ≠ 0 := by
    rw [← hlam]
    exact hsum.ne'
  rw [hψ]
  refine ⟨fun j hj ↦ ?_, fun j hj ↦ ?_⟩
  · have := lt_of_lt_of_eq j.isLt (pow_zero 2)
    omega
  · have hj0 : j = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    have hwj : w ⟨j.val, hj⟩ = w 0 := congrArg w (Subsingleton.elim _ _)
    rw [prepareIndexProb_basisState, ite_eq_left hj0, hwj, hlam, div_self hw0, Rat.cast_one,
      sub_self, abs_zero]
    positivity

/-- Not vacuous: for two equal weights (`b = 1`, `L = 2`, no garbage) and `μ ≥ 1`, the state `|0⟩`,
whose index is `0` with probability `1` instead of `1 / 2`, does not have the property. -/
theorem prepareApproximates_zero_not (μ : ℕ) (hμ : 1 ≤ μ) :
    ¬ PrepareApproximates 1 0 2 μ ![1, 1] (basisState 0) := by
  rintro ⟨-, h⟩
  have h0 := h 0 (by decide)
  have hψ : (basisState 0 : Fin (2 ^ (1 + 0)) → ℂ) = basisState (prepareDataEquiv 1 0 (0, 0)) := by
    rw [prepareDataEquiv_zero]
  have hlam : prepareLambda (![1, 1] : PrepareWeights 2) = 2 := by
    norm_num [prepareLambda, Fin.sum_univ_two]
  have hw0 : (![1, 1] : PrepareWeights 2) ⟨(0 : Fin (2 ^ 1)).val, by decide⟩ = 1 := rfl
  rw [hψ, prepareIndexProb_basisState, ite_eq_left rfl, hw0, hlam] at h0
  have hc : (((1 : ℚ) / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
  have hL : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [hc, hL] at h0
  have hpow : (2 : ℝ) ≤ 2 ^ μ := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ μ := pow_le_pow_right₀ (by norm_num) hμ
  have hle : (1 : ℝ) / (2 ^ μ * 2) ≤ 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have habs := le_abs_self ((1 : ℝ) - 1 / 2)
  linarith

end QuantumComputation.Specs

/-
The next block (up to the line `end QuantumComputation.Specs` before the PREPARE specification)
is the SELECT baseline `QuantumSolutions/BlockEncoding/SelectPauli.lean`, lines 86 to 2075, copied unchanged and
used as a library: the PREPARE lookup circuit is its `SELECT` circuit.

The section between `BEGIN GOOGLE-DERIVED` and `END GOOGLE-DERIVED` is copied (through this repository's
`TableLookup.lean`) from google-deepmind/formal-quantum-computation, branch `discoveries`, commit a88de8f,
files `QuantumComputationDiscoveries/Primitives/Arcsin/Solution/{LowerKraus,StepSemantics}.lean`.
Copyright 2026 Google LLC, licensed under the Apache License, Version 2.0. Modification: the
namespace `ArcsinImpl` is renamed to `SelectPauliSteps` and only the declarations this file
needs are kept.
-/

/-! BEGIN GOOGLE-DERIVED (LowerKraus.lean) -/

namespace QuantumComputation.Specs

namespace SelectPauliSteps

variable {Var : Type}

open Operator Matrix QProg Function
open scoped Matrix ComplexOrder MatrixOrder


section KrausBound

open HermitianMat

variable {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]

/-- `R` is an averaged Kraus lower bound of `P`: `Rᴴ A R ≤ wp P A` for every
store-independent postcondition `A` and every store. -/
def LowerKraus (P : QProg Var d) (R : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ (A : Observable (Fin d)) (σ : Store Var), A.1.conj Rᴴ ≤ (wp P (fun _ ↦ A) σ).1

theorem lowerKraus_qAssign (U : Unitary d) : LowerKraus (Var := Var) (.qAssign U) U.1 := by
  intro A σ
  apply le_of_eq
  ext1
  simp [wp, Matrix.star_eq_conjTranspose]

theorem lowerKraus_skip : LowerKraus (Var := Var) (d := d) .skip 1 := by
  intro A σ
  simp [wp]

namespace LowerKraus

variable {P Q : QProg Var d} {R R₁ R₂ : Matrix (Fin d) (Fin d) ℂ}

theorem conj_le_one (h : LowerKraus P R) (A : Observable (Fin d)) : A.1.conj Rᴴ ≤ 1 :=
  (conj_mono A.2.2).trans ((h 1 (fun _ ↦ 0)).trans (wp P (fun _ ↦ 1) (fun _ ↦ 0)).2.2)

/-- The observable `Rᴴ A R` attached to a lower bound. -/
noncomputable def conjObs (h : LowerKraus P R) (A : Observable (Fin d)) : Observable (Fin d) :=
  ⟨A.1.conj Rᴴ, conj_nonneg _ A.2.1, h.conj_le_one A⟩

theorem qSeq (h₁ : LowerKraus P R₁) (h₂ : LowerKraus Q R₂) :
    LowerKraus (P.qSeq Q) (R₂ * R₁) := by
  intro A σ
  have hmono : (fun _ ↦ h₂.conjObs A) ≤ wp Q (fun _ ↦ A) := fun σ' ↦ h₂ A σ'
  calc A.1.conj (R₂ * R₁)ᴴ = (h₂.conjObs A).1.conj R₁ᴴ := by
        rw [conjObs, conj_conj, conjTranspose_mul]
    _ ≤ (wp P (fun _ ↦ h₂.conjObs A) σ).1 := h₁ _ σ
    _ ≤ (wp P (wp Q (fun _ ↦ A)) σ).1 := wp_mono P hmono σ

end LowerKraus

/-- The real scalar `√½` as a complex number. -/
noncomputable abbrev sqrtHalf : ℂ := (Real.sqrt (1 / 2) : ℝ)

theorem sqrtHalf_mul_sqrtHalf : sqrtHalf * sqrtHalf = 1 / 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast
  ring

omit [NeZero d] in
private theorem conj_add_conj_eq (A : HermitianMat (Fin d) ℂ) (B₀ B₁ : Matrix (Fin d) (Fin d) ℂ) :
    A.conj B₀ᴴ + A.conj B₁ᴴ =
      A.conj (sqrtHalf • (B₀ + B₁))ᴴ + A.conj (sqrtHalf • (B₀ - B₁))ᴴ := by
  ext1
  have hs : star sqrtHalf = sqrtHalf := Complex.conj_ofReal _
  simp only [HermitianMat.mat_add, conj_apply_mat, conjTranspose_conjTranspose,
    conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, conjTranspose_add,
    conjTranspose_sub, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub]
  match_scalars <;> first | ring1 | linear_combination (-2 : ℂ) * sqrtHalf_mul_sqrtHalf

/-- Measurement-based correction: measuring with a two-outcome measurement `ℳ` into `v`,
then applying `F` on outcome `1`, admits the averaged bound `√½ (M₀ + R_F M₁)`. -/
theorem lowerKraus_measure_qIf (v : Var) (ℳ : Measurement d 2) {F : QProg Var d}
    {R_F : Matrix (Fin d) (Fin d) ℂ} (hF : LowerKraus F R_F) :
    LowerKraus ((QProg.qMeasure v ℳ).qSeq (.qIf (fun σ ↦ σ v = 1) F .skip))
      (sqrtHalf • (ℳ.1 0 + R_F * ℳ.1 1)) := by
  intro A σ
  have hwp : (wp ((QProg.qMeasure v ℳ).qSeq (.qIf (fun σ ↦ σ v = 1) F .skip))
      (fun _ ↦ A) σ).1 =
      A.1.conj (ℳ.1 0)ᴴ + (wp F (fun _ ↦ A) (Store.subst σ v 1)).1.conj (ℳ.1 1)ᴴ := by
    simp only [wp, CQAssertion.qMeasure_coe, Fin.sum_univ_two]
    simp [Store.subst]
  rw [hwp]
  calc A.1.conj (sqrtHalf • (ℳ.1 0 + R_F * ℳ.1 1))ᴴ
      ≤ A.1.conj (sqrtHalf • (ℳ.1 0 + R_F * ℳ.1 1))ᴴ +
          A.1.conj (sqrtHalf • (ℳ.1 0 - R_F * ℳ.1 1))ᴴ :=
        le_add_of_nonneg_right (conj_nonneg _ A.2.1)
    _ = A.1.conj (ℳ.1 0)ᴴ + (A.1.conj R_Fᴴ).conj (ℳ.1 1)ᴴ := by
        rw [← conj_add_conj_eq, conj_conj, conjTranspose_mul]
    _ ≤ _ := add_le_add_right (conj_mono (hF A _)) _

/-- An averaged lower bound `R` whose clean-ancilla restriction agrees with the intended unitary
`E = rTarget.embedUnitary U` (i.e. `Π₀ R = Π₀ E Π₀`) yields a clean subroutine. -/
theorem realizesCleanSubroutine_of_lowerKraus {n k m : ℕ} [NeZero (2 ^ n)]
    (rTarget : QRegister k n) (rAnc : QRegister m n) (hdisj : rTarget.DisjointWires rAnc)
    (U : Unitary (2 ^ k)) {P : QProg Var (2 ^ n)} {R : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hP : LowerKraus P R)
    (hR : rAnc.basisOutcomeProjector 0 * R =
      rAnc.basisOutcomeProjector 0 * (rTarget.embedUnitary U).1 *
        rAnc.basisOutcomeProjector 0) :
    RealizesCleanSubroutine rTarget rAnc hdisj U P := by
  intro M
  apply Triple.of_le_wp
  intro σ
  change (CQAssertion.restrictToZeroAncilla _ rAnc σ).1 ≤ (wp P _ σ).1
  refine le_trans (le_of_eq ?_) (hP (CQAssertion.restrictToZeroAncilla (fun _ ↦ M) rAnc σ) σ)
  have hR' : Rᴴ * rAnc.basisOutcomeProjector 0 =
      rAnc.basisOutcomeProjector 0 * (rTarget.embedUnitary U).1ᴴ *
        rAnc.basisOutcomeProjector 0 := by
    simpa [conjTranspose_mul, Matrix.mul_assoc] using congrArg conjTranspose hR
  have hpost : (CQAssertion.restrictToZeroAncilla (fun _ ↦ M) rAnc σ).1 =
      M.1.conj (rAnc.basisOutcomeProjector 0) := rfl
  have hpre : (CQAssertion.restrictToZeroAncilla
      (CQAssertion.qAssign (rTarget.embedUnitary U)
        (CQAssertion.restrictToZeroAncilla (fun _ ↦ M) rAnc))
      rAnc σ).1 = ((M.1.conj (rAnc.basisOutcomeProjector 0)).conj
        (star (rTarget.embedUnitary U)).1).conj (rAnc.basisOutcomeProjector 0) := rfl
  rw [hpre, hpost, conj_conj, conj_conj, conj_conj, hR', Unitary.coe_star,
    Matrix.star_eq_conjTranspose]

end KrausBound

variable {n k : ℕ}

abbrev basisBitsEquiv (q : ℕ) : Fin (2 ^ q) ≃ BitAssignment q := basisBits q

/-- Computational-basis vector with bit assignment `β`. -/
noncomputable abbrev ket (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  basisState ((basisBits n).symm β)

@[simp]
theorem basisBits_basisBitsEquiv_symm (q : ℕ) (β : BitAssignment q) :
    basisBits q ((basisBits q).symm β) = β :=
  (basisBits q).apply_symm_apply β

@[simp]
theorem basisBitsEquiv_symm_basisBits (q : ℕ) (j : Fin (2 ^ q)) :
    (basisBits q).symm (basisBits q j) = j :=
  (basisBits q).symm_apply_apply j

theorem single_eq_ket (g : Fin (2 ^ n)) :
    (Pi.single g 1 : Fin (2 ^ n) → ℂ) = ket (basisBits n g) := by
  simp [ket]

/-- Overwrite the bits selected by `r` with `γ`. -/
noncomputable def writeReg (β : BitAssignment n) (r : QRegister k n) (γ : BitAssignment k) :
    BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBits n).symm β) ((basisBits k).symm γ))

@[simp]
theorem writeReg_apply_reg (β : BitAssignment n) (r : QRegister k n) (γ : BitAssignment k)
    (i : Fin k) : writeReg β r γ (r i) = γ i := by
  simp [writeReg, QRegister.basisBits_replaceIndex_apply]

theorem writeReg_apply_of_not_mem (β : BitAssignment n) (r : QRegister k n) (γ : BitAssignment k)
    (w : Wire n) (hw : w ∉ Set.range r.wires) : writeReg β r γ w = β w := by
  simp [writeReg, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]

/-- Writing a register that agrees with `β` except at position `i₀` is a single-bit update. -/
theorem writeReg_eq_update (β : BitAssignment n) (r : QRegister k n) (γ : BitAssignment k)
    (i₀ : Fin k) (hγ : ∀ i, i ≠ i₀ → γ i = β (r i)) :
    writeReg β r γ = Function.update β (r i₀) (γ i₀) := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    rw [writeReg_apply_reg]
    by_cases hi : i = i₀
    · subst hi
      simp
    · rw [Function.update_of_ne (fun h ↦ hi (r.wires.injective h)), hγ i hi]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw, Function.update_of_ne]
    exact fun h ↦ hw ⟨i₀, h.symm⟩

/-- Local basis index read through a register. -/
noncomputable abbrev localIdx (r : QRegister k n) (β : BitAssignment n) : Fin (2 ^ k) :=
  (basisBits k).symm (fun i ↦ β (r i))

@[simp]
theorem localIdx_writeReg (β : BitAssignment n) (r : QRegister k n) (γ : BitAssignment k) :
    localIdx r (writeReg β r γ) = (basisBits k).symm γ := by
  simp [localIdx]

theorem localIdx_writeReg_of_disjoint {m : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (s : QRegister m n) (hdisj : r.DisjointWires s) (γ : BitAssignment k) :
    localIdx s (writeReg β r γ) = localIdx s β := by
  simp only [localIdx]
  congr 1
  funext i
  exact writeReg_apply_of_not_mem _ _ _ _ fun hw ↦ Set.disjoint_left.1 hdisj hw ⟨i, rfl⟩

@[simp]
theorem writeReg_writeReg (β : BitAssignment n) (r : QRegister k n) (γ γ' : BitAssignment k) :
    writeReg (writeReg β r γ) r γ' = writeReg β r γ' := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    rw [writeReg_apply_reg, writeReg_apply_reg]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw, writeReg_apply_of_not_mem _ _ _ _ hw,
      writeReg_apply_of_not_mem _ _ _ _ hw]

@[simp]
theorem writeReg_self (β : BitAssignment n) (r : QRegister k n) :
    writeReg β r (fun i ↦ β (r i)) = β := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    rw [writeReg_apply_reg]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw]

/-- An embedded local matrix acting on a basis ket. -/
theorem embedMatrix_mulVec_ket (r : QRegister k n) (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ)
    (β : BitAssignment n) :
    (r.embedMatrix A).mulVec (ket β) =
      ∑ l : Fin (2 ^ k), A l (localIdx r β) • ket (writeReg β r (basisBits k l)) := by
  have hext : r.extractIndex ((basisBits n).symm β) = localIdx r β := by
    simp [QRegister.extractIndex]
  have hcol (j : Fin (2 ^ k)) :
      A.mulVec (Pi.single j 1) = ∑ l : Fin (2 ^ k), A l j • Pi.single l 1 := by
    funext x
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [ket, basisState, r.embedMatrix_mulVec_single_factors, hext, hcol,
    QRegister.tensorState_sum_left]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex]
  simp [writeReg, ket, basisState]

/-- An embedded permutation matrix maps a basis ket to a basis ket. -/
theorem embedMatrix_permMatrix_mulVec_ket (r : QRegister k n) (σ : Equiv.Perm (Fin (2 ^ k)))
    (β : BitAssignment n) :
    (r.embedMatrix (σ.permMatrix ℂ)).mulVec (ket β) =
      ket (writeReg β r (basisBits k (σ.symm (localIdx r β)))) := by
  rw [embedMatrix_mulVec_ket, Finset.sum_eq_single (σ.symm (localIdx r β))]
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  · intro l _ hl
    have : σ l ≠ localIdx r β := fun h ↦ hl (by rw [← h, Equiv.symm_apply_apply])
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, this]
  · simp

/-- An embedded one-qubit matrix acting on a basis ket. -/
theorem singleton_embedMatrix_mulVec_ket (q : Wire n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (β : BitAssignment n) :
    ((QRegister.singleton q).embedMatrix A).mulVec (ket β) =
      A 0 (if β q = 0 then 0 else 1) • ket (Function.update β q 0) +
        A 1 (if β q = 0 then 0 else 1) • ket (Function.update β q 1) := by
  have hloc : localIdx (QRegister.singleton q) β = if β q = 0 then 0 else 1 := by
    have h : ∀ b : ZMod 2,
        ((basisBits 1).symm (fun _ ↦ b) : Fin 2) = if b = 0 then 0 else 1 := by decide
    exact h (β q)
  have hw (l : Fin 2) (b : ZMod 2) (hb : basisBits 1 l = fun _ ↦ b) :
      writeReg β (QRegister.singleton q) (basisBits 1 l) = Function.update β q b := by
    rw [writeReg_eq_update _ _ _ 0 (fun i hi ↦ absurd (Subsingleton.elim i 0) hi), hb]
    rfl
  rw [embedMatrix_mulVec_ket, hloc]
  change ∑ l : Fin 2, _ = _
  rw [Fin.sum_univ_two, hw 0 0 (by decide), hw 1 1 (by decide)]

/-- Sign `(-1)^b` of a bit. -/
abbrev bitSign (b : ZMod 2) : ℂ := if b = 0 then 1 else -1

theorem bit_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem one_add_one_zmod2 : (1 : ZMod 2) + 1 = 0 := rfl

theorem ket_X (q : Wire n) (β : BitAssignment n) :
    (Circuit.X q).eval.1.mulVec (ket β) = ket (Function.update β q (β q + 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![0, 1; 1, 0]).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  rcases bit_cases (β q) with hb | hb <;> simp [hb, one_add_one_zmod2]

theorem ket_Z (q : Wire n) (β : BitAssignment n) :
    (Circuit.Z q).eval.1.mulVec (ket β) = bitSign (β q) • ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![1, 0; 0, -1]).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  rcases bit_cases (β q) with hb | hb <;> rw [hb] at e <;> simp [hb, e]

/-- Phase `i^b` of a bit. -/
abbrev bitPhaseI (b : ZMod 2) : ℂ := if b = 0 then 1 else Complex.I

theorem ket_S (q : Wire n) (β : BitAssignment n) :
    (Circuit.S q).eval.1.mulVec (ket β) = bitPhaseI (β q) • ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![1, 0; 0, Complex.I]).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  rcases bit_cases (β q) with hb | hb <;> rw [hb] at e <;> simp [hb, e]

theorem ket_H (q : Wire n) (β : BitAssignment n) :
    (Circuit.H q).eval.1.mulVec (ket β) =
      (Real.sqrt (1 / 2) : ℂ) • (ket (Function.update β q 0) +
        bitSign (β q) • ket (Function.update β q 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix
    ((Real.sqrt (1 / 2) : ℝ) • !![(1 : ℂ), 1; 1, -1])).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  rcases bit_cases (β q) with hb | hb <;> simp [hb, smul_add, Complex.real_smul]

theorem ket_CNOT (c t : Wire n) (h : c ≠ t) (β : BitAssignment n) :
    (Circuit.CNOT c t h).eval.1.mulVec (ket β) = ket (Function.update β t (β t + β c)) := by
  rw [Circuit.eval_gate, QRegister.embedUnitary_val, PrimitiveGate.eval_cnot_val,
    embedMatrix_permMatrix_mulVec_ket]
  have hloc : ∀ γ : BitAssignment 2,
      basisBits 2 ((Equiv.swap (1 : Fin 4) 3).symm ((basisBits 2).symm γ)) =
        Function.update γ 1 (γ 1 + γ 0) := by decide
  rw [localIdx, hloc, writeReg_eq_update _ _ _ 1]
  · simp
  · intro i hi
    fin_cases i
    · simp
    · exact absurd rfl hi

/-- Exact single-qubit inverse `T† = Z · S · T` using `1` `T` gate and `0` `TOFF` gates. -/
def T_dag (q : Wire n) : Circuit n :=
  .seq (Circuit.Z q) (.seq (Circuit.S q) (Circuit.T q))

/-- Clean-ancilla 4-`T` AND gate on wires `c₁, c₂, t` (`4` `T` gates, `0` `TOFF` gates). -/
def AND4T (c₁ c₂ t : Wire n) (_h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) : Circuit n :=
  .seq (Circuit.H t)
    (.seq (Circuit.CNOT c₂ t h₂t)
      (.seq (T_dag t)
        (.seq (Circuit.CNOT c₁ t h₁t)
          (.seq (Circuit.T t)
            (.seq (Circuit.CNOT c₂ t h₂t)
              (.seq (T_dag t)
                (.seq (Circuit.CNOT c₁ t h₁t)
                  (.seq (Circuit.T t)
                    (.seq (Circuit.H t) (Circuit.S t))))))))))

/-- Monomial phase of `AND4T` on computational basis inputs `a, b, c : ZMod 2`
(`+1` whenever `c = 0`). -/
noncomputable def cleanAndPhase (a b c : ZMod 2) : ℂ :=
  if c = 0 then 1 else if a * b = 1 then -Complex.I else Complex.I

theorem count_T_AND4T (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (AND4T c₁ c₂ t h₁₂ h₁t h₂t).count PrimitiveGate.T = 4 := rfl

theorem count_TOFF_AND4T (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (AND4T c₁ c₂ t h₁₂ h₁t h₂t).count PrimitiveGate.TOFF = 0 := rfl

noncomputable abbrev bitPhaseT (b : ZMod 2) : ℂ :=
  if b = 0 then 1 else (1 + Complex.I) / (Real.sqrt 2 : ℂ)

theorem ket_T (q : Wire n) (β : BitAssignment n) :
    (Circuit.T q).eval.1.mulVec (ket β) = bitPhaseT (β q) • ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix
    !![1, 0; 0, (1 + Complex.I) / (Real.sqrt 2 : ℂ)]).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  rcases bit_cases (β q) with hb | hb <;> rw [hb] at e <;> simp [hb, e]

theorem seq_mulVec (c₁ c₂ : Circuit n) (ψ : Fin (2 ^ n) → ℂ) :
    (c₁.seq c₂).eval.1.mulVec ψ = c₂.eval.1.mulVec (c₁.eval.1.mulVec ψ) := by
  rw [Circuit.eval_seq, Matrix.mulVec_mulVec]
  rfl

theorem ket_T_dag (q : Wire n) (β : BitAssignment n) :
    (T_dag q).eval.1.mulVec (ket β) =
      (bitSign (β q) * (bitPhaseI (β q) * bitPhaseT (β q))) • ket β := by
  simp only [T_dag, seq_mulVec, ket_Z, ket_S, ket_T, Matrix.mulVec_smul, smul_smul]

theorem ket_AND4T_eq_smul (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment n) :
    (AND4T c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec (ket β) =
      cleanAndPhase (β c₁) (β c₂) (β t) • ket (Function.update β t (β t + β c₁ * β c₂)) := by
  have hs2 : (Real.sqrt (1 / 2) : ℂ) ^ 2 = 1 / 2 := by
    norm_cast
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  have h2 : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = 1 / 2 := by
    rw [inv_pow]
    norm_cast
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h4 : ((Real.sqrt 2 : ℂ)⁻¹) ^ 4 = 1 / 4 := by
    linear_combination ((Real.sqrt 2 : ℂ)⁻¹ ^ 2 + 1 / 2) * h2
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hi3 : Complex.I ^ 3 = -Complex.I := by
    linear_combination Complex.I * hi2
  have hi4 : Complex.I ^ 4 = 1 := by
    linear_combination (Complex.I ^ 2 - 1) * hi2
  have hi5 : Complex.I ^ 5 = Complex.I := by
    linear_combination (Complex.I ^ 3 - Complex.I) * hi2
  have hi6 : Complex.I ^ 6 = -1 := by
    linear_combination (Complex.I ^ 4 - Complex.I ^ 2 + 1) * hi2
  have hi7 : Complex.I ^ 7 = -Complex.I := by
    linear_combination (Complex.I ^ 5 - Complex.I ^ 3 + Complex.I) * hi2
  simp only [AND4T, seq_mulVec, ket_H, ket_CNOT, ket_T, ket_T_dag, ket_S,
    Matrix.mulVec_smul, Matrix.mulVec_add, smul_add, smul_smul,
    Function.update_idem, Function.update_self,
    Function.update_of_ne h₁t, Function.update_of_ne h₂t]
  rcases bit_cases (β c₁) with h₁ | h₁ <;>
    rcases bit_cases (β c₂) with h₂ | h₂ <;>
    rcases bit_cases (β t) with ht | ht <;>
    simp only [h₁, h₂, ht, one_add_one_zmod2, cleanAndPhase, bitSign, bitPhaseI, bitPhaseT,
      zero_ne_one, one_ne_zero, ↓reduceIte, zero_add, add_zero, mul_zero, one_mul, mul_one] <;>
    match_scalars <;>
    ring_nf <;>
    simp only [hs2, h2, h4, hi2, hi3, hi4, hi5, hi6, hi7] <;>
    ring


/-- 4-`T` relative-phase Toffoli gate with phase `+1` whenever `a * b * c = 0`. -/
def RCCX0 (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) : Circuit n :=
  .seq (Circuit.Z t) (.seq (Circuit.S t) (AND4T c₁ c₂ t h₁₂ h₁t h₂t))

/-- 4-`T` relative-phase Toffoli gate with phase `+1` whenever `a * b * (c + 1) = 0`. -/
def RCCX1 (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) : Circuit n :=
  .seq (Circuit.X t) (.seq (RCCX0 c₁ c₂ t h₁₂ h₁t h₂t) (Circuit.X t))

noncomputable def rccx0Phase (a b c : ZMod 2) : ℂ :=
  bitSign c * (bitPhaseI c * cleanAndPhase a b c)

theorem rccx0Phase_eq_one {a b c : ZMod 2} (h : a * b * c = 0) : rccx0Phase a b c = 1 := by
  rcases bit_cases a with rfl | rfl <;>
    rcases bit_cases b with rfl | rfl <;>
    rcases bit_cases c with rfl | rfl <;>
    simp_all [rccx0Phase, bitSign, bitPhaseI, cleanAndPhase, Complex.I_mul_I]

theorem count_T_RCCX0 (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (RCCX0 c₁ c₂ t h₁₂ h₁t h₂t).count PrimitiveGate.T = 4 := rfl

theorem count_TOFF_RCCX0 (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (RCCX0 c₁ c₂ t h₁₂ h₁t h₂t).count PrimitiveGate.TOFF = 0 := rfl

theorem count_T_RCCX1 (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (RCCX1 c₁ c₂ t h₁₂ h₁t h₂t).count PrimitiveGate.T = 4 := rfl

theorem count_TOFF_RCCX1 (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (RCCX1 c₁ c₂ t h₁₂ h₁t h₂t).count PrimitiveGate.TOFF = 0 := rfl

theorem ket_RCCX0_eq_smul (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment n) :
    (RCCX0 c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec (ket β) =
      rccx0Phase (β c₁) (β c₂) (β t) • ket (Function.update β t (β t + β c₁ * β c₂)) := by
  simp only [RCCX0, seq_mulVec, ket_Z, ket_S, ket_AND4T_eq_smul, Matrix.mulVec_smul, smul_smul,
    rccx0Phase]

theorem ket_RCCX1_eq_smul (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment n) :
    (RCCX1 c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec (ket β) =
      rccx0Phase (β c₁) (β c₂) (β t + 1) • ket (Function.update β t (β t + β c₁ * β c₂)) := by
  have hadd : ∀ x y : ZMod 2, x + 1 + y + 1 = x + y := by decide
  have hup : Function.update (Function.update (Function.update β t (β t + 1)) t
      (β t + 1 + β c₁ * β c₂)) t (β t + 1 + β c₁ * β c₂ + 1) =
      Function.update β t (β t + β c₁ * β c₂) := by
    rw [Function.update_idem, Function.update_idem, hadd]
  simp only [RCCX1, seq_mulVec, ket_X, ket_RCCX0_eq_smul, Matrix.mulVec_smul,
    Function.update_self, Function.update_of_ne h₁t, Function.update_of_ne h₂t, hup]
/-- Projector onto outcome `o` of a single wire, acting on a basis ket. -/
theorem ket_projector (q : Wire n) (o : Fin 2) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector o).mulVec (ket β) =
      if β q = (o.val : ZMod 2) then ket β else 0 := by
  rw [ket, basisState, QRegister.basisOutcomeProjector_mulVec_single]
  have h : ∀ (b : ZMod 2) (o : Fin 2),
      (((basisBits 1).symm (fun _ ↦ b) : Fin 2) = o ↔ b = (o.val : ZMod 2)) := by decide
  have hext : (QRegister.singleton q).extractIndex ((basisBits n).symm β) =
      (basisBits 1).symm (fun _ ↦ β q) := by
    simp [QRegister.extractIndex]
  simp only [hext]
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd ((h _ _).1 h1) h2 |
    exact absurd ((h _ _).2 h2) h1

theorem ket_projector_zero (q : Wire n) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector 0).mulVec (ket β) =
      if β q = 0 then ket β else 0 :=
  ket_projector q 0 β

theorem ket_projector_one (q : Wire n) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector 1).mulVec (ket β) =
      if β q = 1 then ket β else 0 :=
  ket_projector q 1 β

/-- Two matrices agreeing on every basis ket are equal. -/
theorem matrix_ext_ket {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β, A.mulVec (ket β) = B.mulVec (ket β)) : A = B := by
  ext i j
  have := congrFun (h (basisBits n j)) i
  simpa [← single_eq_ket, Matrix.mulVec_single_one] using this

/-- A register outcome projector acting on a basis ket. -/
theorem basisOutcomeProjector_mulVec_ket (r : QRegister k n) (o : Fin (2 ^ k))
    (β : BitAssignment n) :
    (r.basisOutcomeProjector o).mulVec (ket β) = if localIdx r β = o then ket β else 0 := by
  have hext : r.extractIndex ((basisBits n).symm β) = localIdx r β := by
    simp [QRegister.extractIndex]
  rw [ket, basisState, QRegister.basisOutcomeProjector_mulVec_single, hext]

variable {n : ℕ}

/-- Basis ket of an optional bit assignment, `0` for `none`. -/
noncomputable def optKet : Option (BitAssignment n) → Fin (2 ^ n) → ℂ
  | none => 0
  | some β => ket β

theorem lowerKraus_circuit [DecidableEq Var] [NeZero (2 ^ n)] (c : Circuit n) :
    LowerKraus (Var := Var) c.compile c.eval.1 := by
  induction c with
  | identity => exact lowerKraus_skip
  | gate g r => exact lowerKraus_qAssign _
  | seq c₁ c₂ ih₁ ih₂ => exact ih₁.qSeq ih₂

theorem eval_seq_mulVec (c₁ c₂ : Circuit n) (ψ : Fin (2 ^ n) → ℂ) :
    (Circuit.seq c₁ c₂).eval.1.mulVec ψ = c₂.eval.1.mulVec (c₁.eval.1.mulVec ψ) := by
  rw [Circuit.eval_seq, Matrix.mulVec_mulVec]
  rfl

/-- Phase correction `CZ(c₁, c₂)` (from `S`, `Z` and `CNOT`) followed by `X t`. -/
def fixup (c₁ c₂ t : Wire n) (h : c₁ ≠ c₂) : Circuit n :=
  .seq (Circuit.S c₁) (.seq (Circuit.S c₂) (.seq (Circuit.CNOT c₁ c₂ h) (.seq (Circuit.S c₂)
    (.seq (Circuit.Z c₂) (.seq (Circuit.CNOT c₁ c₂ h) (Circuit.X t))))))

theorem phase_cz (a b : ZMod 2) :
    bitPhaseI a * bitPhaseI b * bitPhaseI (b + a) * bitSign (b + a) = bitSign (a * b) := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    simp [bitPhaseI, bitSign, one_add_one_zmod2, Complex.I_mul_I]

theorem fixup_mulVec_ket (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (β : BitAssignment n) :
    (fixup c₁ c₂ t h₁₂).eval.1.mulVec (ket β) =
      bitSign (β c₁ * β c₂) • ket (update β t (β t + 1)) := by
  have hβ : update (update β c₂ (β c₂ + β c₁)) c₂ (β c₂ + β c₁ + β c₁) = β := by
    rw [update_idem, add_assoc, CharTwo.add_self_eq_zero, add_zero, update_eq_self]
  simp only [fixup, eval_seq_mulVec, ket_S, ket_Z, ket_CNOT, ket_X, Matrix.mulVec_smul,
    update_self, update_of_ne h₁₂, hβ, smul_smul]
  rw [← phase_cz]
  ring_nf

theorem lowerKraus_measure_singleton_qIf [DecidableEq Var] [NeZero (2 ^ n)]
    (v : Var) (t : Wire n) {F : QProg Var (2 ^ n)} {R_F : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hF : LowerKraus F R_F) :
    LowerKraus ((QProg.measureRegister v (QRegister.singleton t)).qSeq
        (.qIf (fun σ ↦ σ v = 1) F .skip))
      (sqrtHalf • ((QRegister.singleton t).basisOutcomeProjector 0 +
        R_F * (QRegister.singleton t).basisOutcomeProjector 1)) :=
  lowerKraus_measure_qIf v _ hF

/-- Phase correction `Z(c_1) ... Z(c_m)` followed by `X t` for single-wire BGL parity
uncomputation. -/
def fixupZ : List (Wire n) → Wire n → Circuit n
  | [], t => Circuit.X t
  | c :: cs, t => .seq (Circuit.Z c) (fixupZ cs t)

theorem count_T_fixupZ (sources : List (Wire n)) (t : Wire n) :
    (fixupZ sources t).count PrimitiveGate.T = 0 := by
  induction sources with
  | nil => simp [fixupZ]
  | cons _ _ ih => simp [fixupZ, ih]

theorem count_TOFF_fixupZ (sources : List (Wire n)) (t : Wire n) :
    (fixupZ sources t).count PrimitiveGate.TOFF = 0 := by
  induction sources with
  | nil => simp [fixupZ]
  | cons _ _ ih => simp [fixupZ, ih]

theorem bitSign_add (a b : ZMod 2) : bitSign (a + b) = bitSign a * bitSign b := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    simp [bitSign, one_add_one_zmod2]

theorem fixupZ_mulVec_ket (sources : List (Wire n)) (t : Wire n) (β : BitAssignment n) :
    (fixupZ sources t).eval.1.mulVec (ket β) =
      bitSign ((sources.map β).sum) • ket (update β t (β t + 1)) := by
  induction sources with
  | nil =>
    simp only [fixupZ, List.map_nil, List.sum_nil, bitSign, ↓reduceIte, one_smul]
    exact ket_X t β
  | cons c cs ih =>
    simp only [fixupZ, eval_seq_mulVec, ket_Z, Matrix.mulVec_smul, ih, smul_smul,
      List.map_cons, List.sum_cons, bitSign_add]

/-- Phase correction `CZ(c₁, c₂)` (from `S`, `Z` and `CNOT`). -/
def fixupCZ (c₁ c₂ : Wire n) : Circuit n :=
  if h : c₁ ≠ c₂ then
    .seq (Circuit.S c₁) (.seq (Circuit.S c₂) (.seq (Circuit.CNOT c₁ c₂ h) (.seq (Circuit.S c₂)
      (.seq (Circuit.Z c₂) (Circuit.CNOT c₁ c₂ h)))))
  else
    .identity

theorem count_T_fixupCZ (c₁ c₂ : Wire n) :
    (fixupCZ c₁ c₂).count PrimitiveGate.T = 0 := by
  unfold fixupCZ; split_ifs <;> simp

theorem count_TOFF_fixupCZ (c₁ c₂ : Wire n) :
    (fixupCZ c₁ c₂).count PrimitiveGate.TOFF = 0 := by
  unfold fixupCZ; split_ifs <;> simp

theorem fixupCZ_mulVec_ket (c₁ c₂ : Wire n) (h₁₂ : c₁ ≠ c₂) (β : BitAssignment n) :
    (fixupCZ c₁ c₂).eval.1.mulVec (ket β) =
      bitSign (β c₁ * β c₂) • ket β := by
  have hβ : update (update β c₂ (β c₂ + β c₁)) c₂ (β c₂ + β c₁ + β c₁) = β := by
    rw [update_idem, add_assoc, CharTwo.add_self_eq_zero, add_zero, update_eq_self]
  simp only [fixupCZ, dite_eq_left h₁₂, eval_seq_mulVec, ket_S, ket_Z, ket_CNOT, Matrix.mulVec_smul,
    update_self, update_of_ne h₁₂, hβ, smul_smul]
  rw [← phase_cz]
  ring_nf

/-- Phase correction `CZ(p_1) ... CZ(p_k) Z(c_1) ... Z(c_m)` followed by `X t` for quadratic +
linear BGL uncomputation. -/
def fixupQuad : List (Wire n × Wire n) → List (Wire n) → Wire n → Circuit n
  | [], lins, t => fixupZ lins t
  | (c₁, c₂) :: qs, lins, t => .seq (fixupCZ c₁ c₂) (fixupQuad qs lins t)

theorem count_T_fixupQuad (quads : List (Wire n × Wire n)) (lins : List (Wire n)) (t : Wire n) :
    (fixupQuad quads lins t).count PrimitiveGate.T = 0 := by
  induction quads with
  | nil => exact count_T_fixupZ lins t
  | cons p qs ih => simp [fixupQuad, count_T_fixupCZ, ih]

theorem count_TOFF_fixupQuad (quads : List (Wire n × Wire n)) (lins : List (Wire n)) (t : Wire n) :
    (fixupQuad quads lins t).count PrimitiveGate.TOFF = 0 := by
  induction quads with
  | nil => exact count_TOFF_fixupZ lins t
  | cons p qs ih => simp [fixupQuad, count_TOFF_fixupCZ, ih]

theorem fixupQuad_mulVec_ket (quads : List (Wire n × Wire n)) (lins : List (Wire n)) (t : Wire n)
    (hneq : ∀ p ∈ quads, p.1 ≠ p.2) (β : BitAssignment n) :
    (fixupQuad quads lins t).eval.1.mulVec (ket β) =
      bitSign ((quads.map (fun p ↦ β p.1 * β p.2)).sum + (lins.map β).sum) •
        ket (update β t (β t + 1)) := by
  induction quads with
  | nil =>
    simp only [fixupQuad, List.map_nil, List.sum_nil, zero_add]
    exact fixupZ_mulVec_ket lins t β
  | cons p qs ih =>
    have hp : p.1 ≠ p.2 := hneq p (List.mem_cons_self ..)
    have hqs : ∀ q ∈ qs, q.1 ≠ q.2 := fun q hq ↦ hneq q (List.mem_cons_of_mem _ hq)
    simp only [fixupQuad, eval_seq_mulVec, fixupCZ_mulVec_ket p.1 p.2 hp, Matrix.mulVec_smul,
      ih hqs, smul_smul, List.map_cons, List.sum_cons, add_assoc, bitSign_add]



variable {n k : ℕ}

/-- A register without its first wire. -/
abbrev regTail (r : QRegister (k + 1) n) : QRegister k n := r.slice 1 k (by omega)

theorem regTail_apply (r : QRegister (k + 1) n) (i : Fin k) : regTail r i = r i.succ := by
  rw [QRegister.slice_apply]
  congr 1
  ext
  simp [add_comm]

theorem regTail_ne_zero (r : QRegister (k + 1) n) (i : Fin k) : regTail r i ≠ r 0 := by
  rw [regTail_apply]
  exact fun h ↦ Fin.succ_ne_zero i (r.wires.injective h)

theorem zero_not_mem_regTail (r : QRegister (k + 1) n) : r 0 ∉ Set.range (regTail r).wires :=
  fun ⟨i, hi⟩ ↦ regTail_ne_zero r i hi

theorem not_mem_regTail {r : QRegister (k + 1) n} {w : Wire n} (hw : w ∉ Set.range r.wires) :
    w ∉ Set.range (regTail r).wires :=
  fun ⟨i, hi⟩ ↦ hw ⟨i.succ, by rw [← hi, regTail_apply]⟩

theorem not_mem_of_disjoint {m : ℕ} {r : QRegister k n} {s : QRegister m n}
    (h : r.DisjointWires s) (i : Fin k) : r i ∉ Set.range s.wires :=
  fun ⟨j, hj⟩ ↦ h.ne i j hj.symm

theorem apply_not_mem_slice (r : QRegister k n) (j : Fin k) (a b : ℕ) (h : a + b ≤ k)
    (hj : (j : ℕ) < a ∨ a + b ≤ j) : r j ∉ Set.range (r.slice a b h).wires := by
  rintro ⟨i, hi⟩
  have := congrArg Fin.val (r.wires.injective ((QRegister.slice_apply r a b h i).symm.trans hi))
  change a + (i : ℕ) = j at this
  omega

theorem writeReg_succ (β : BitAssignment n) (r : QRegister (k + 1) n)
    (γ : BitAssignment (k + 1)) :
    writeReg β r γ = update (writeReg β (regTail r) (fun i ↦ γ i.succ)) (r 0) (γ 0) := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    rw [writeReg_apply_reg]
    cases i using Fin.cases with
    | zero => rw [update_self]
    | succ j =>
      rw [update_of_ne (fun h ↦ Fin.succ_ne_zero j (r.wires.injective h)), ← regTail_apply,
        writeReg_apply_reg]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw, update_of_ne (fun h ↦ hw ⟨0, h.symm⟩),
      writeReg_apply_of_not_mem _ _ _ _ (not_mem_regTail hw)]

theorem writeReg_update_of_not_mem (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) {w : Wire n} (hw : w ∉ Set.range r.wires) (x : ZMod 2) :
    writeReg (update β w x) r γ = update (writeReg β r γ) w x := by
  funext w'
  by_cases hw' : w' ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw'
    rw [writeReg_apply_reg, update_of_ne (fun h ↦ hw ⟨i, h⟩), writeReg_apply_reg]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw']
    by_cases h : w' = w
    · subst h
      rw [update_self, update_self]
    · rw [update_of_ne h, update_of_ne h, writeReg_apply_of_not_mem _ _ _ _ hw']

theorem localIdx_update_of_not_mem (r : QRegister k n) (β : BitAssignment n) {w : Wire n}
    (hw : w ∉ Set.range r.wires) (x : ZMod 2) : localIdx r (update β w x) = localIdx r β := by
  simp only [localIdx]
  congr 1
  funext i
  exact update_of_ne (fun h ↦ hw ⟨i, h⟩) _ _

theorem not_mem_slice {N : ℕ} {r : QRegister N n} {w : Wire n} (hw : w ∉ Set.range r.wires)
    (a b : ℕ) (h : a + b ≤ N) : w ∉ Set.range (r.slice a b h).wires :=
  fun ⟨i, hi⟩ ↦ hw ⟨_, (QRegister.slice_apply r a b h i).symm.trans hi⟩

theorem localIdx_slice_slice {N : ℕ} (r : QRegister N n) (a b c d : ℕ) (h : a + b ≤ N)
    (h' : c + d ≤ b) (β : BitAssignment n) :
    localIdx ((r.slice a b h).slice c d h') β = localIdx (r.slice (a + c) d (by omega)) β := by
  simp only [localIdx, QRegister.slice_apply, Nat.add_assoc]

theorem localIdx_val (r : QRegister k n) (β : BitAssignment n) :
    (localIdx r β : ℕ) = ∑ i : Fin k, (β (r i)).val * 2 ^ (i : ℕ) := by
  simp [localIdx, basisBits, ZMod.finEquiv]
  rfl

theorem localIdx_val_succ (r : QRegister (k + 1) n) (β : BitAssignment n) :
    (localIdx r β : ℕ) = (β (r 0)).val + 2 * (localIdx (regTail r) β : ℕ) := by
  rw [localIdx_val, localIdx_val, Fin.sum_univ_succ, Finset.mul_sum]
  simp only [regTail_apply, Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

theorem localIdx_val_split {N : ℕ} (r : QRegister N n) (a b : ℕ) (h : a + b = N)
    (β : BitAssignment n) :
    (localIdx r β : ℕ) = (localIdx (r.slice 0 a (by omega)) β : ℕ) +
      2 ^ a * (localIdx (r.slice a b (by omega)) β : ℕ) := by
  subst h
  rw [localIdx_val, localIdx_val, localIdx_val, Finset.mul_sum, Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [QRegister.slice_apply, zero_add]
    rfl
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    change (β (r ⟨a + i, by omega⟩)).val * 2 ^ (a + (i : ℕ)) =
      2 ^ a * ((β (r ⟨a + i, by omega⟩)).val * 2 ^ (i : ℕ))
    ring

theorem writeReg_comm {m : ℕ} (β : BitAssignment n) (r : QRegister k n) (s : QRegister m n)
    (hdisj : r.DisjointWires s) (γ : BitAssignment k) (δ : BitAssignment m) :
    writeReg (writeReg β r γ) s δ = writeReg (writeReg β s δ) r γ := by
  funext w
  by_cases hr : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hr
    rw [writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hdisj i), writeReg_apply_reg,
      writeReg_apply_reg]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hr]
    by_cases hs : w ∈ Set.range s.wires
    · obtain ⟨j, rfl⟩ := hs
      rw [writeReg_apply_reg, writeReg_apply_reg]
    · rw [writeReg_apply_of_not_mem _ _ _ _ hs, writeReg_apply_of_not_mem _ _ _ _ hs,
        writeReg_apply_of_not_mem _ _ _ _ hr]

theorem basisBits_mk_apply (m : ℕ) (hm : m < 2 ^ k) (i : Fin k) :
    basisBits k ⟨m, hm⟩ i = ((m / 2 ^ (i : ℕ) % 2 : ℕ) : ZMod 2) :=
  basisBits_eq_div_mod k ⟨m, hm⟩ i

variable {n : ℕ}

end SelectPauliSteps

end QuantumComputation.Specs

/-! END GOOGLE-DERIVED -/

namespace QuantumComputation.Specs

open Operator Matrix

/-!
## Pauli Strings and the Ideal `SELECT` Unitary
-/

/-- A single-qubit Pauli operator. -/
inductive SelectPauli.Pauli where
  | I
  | X
  | Y
  | Z
  deriving DecidableEq, Inhabited

open SelectPauli (Pauli)

/-- The single-qubit unitary of a Pauli: `1`, and the library's `Qubit.X = !![0, 1; 1, 0]`,
`Qubit.Y = !![0, -i; i, 0]`, `Qubit.Z = !![1, 0; 0, -1]`. -/
noncomputable def SelectPauli.Pauli.unitary : Pauli → Unitary (2 ^ 1)
  | .I => 1
  | .X => Qubit.X
  | .Y => Qubit.Y
  | .Z => Qubit.Z

/-- Classical table of `L` signed Pauli strings on `N` qubits: entry `j` is a sign bit `s_j`
(`true` means the factor `-1`) together with a row, whose column `q` is the Pauli that term `j`
applies to system qubit `q`. -/
abbrev SelectPauliTable (L N : ℕ) : Type := Fin L → Bool × (Fin N → Pauli)

/-- The Pauli string `⊗_q σ_q` of a row `σ : Fin N → Pauli`, with no sign or phase: the product
of `σ_q` placed on wire `q` of an `N`-qubit register, for `q = 0, …, N - 1`. The factors act on
distinct wires and commute, so the order of the product does not matter. -/
noncomputable def selectPauliString {N : ℕ} (row : Fin N → Pauli) : Unitary (2 ^ N) :=
  (List.ofFn fun q : Fin N ↦ (QRegister.singleton q).embedUnitary (row q).unitary).prod

/-- The unitary `(-1)^s`, that is `-1` when `s = true` and `1` when `s = false`. -/
noncomputable def selectPauliSign (N : ℕ) (s : Bool) : Unitary (2 ^ N) :=
  if s then
    ⟨-1, by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      simp⟩
  else 1

/-- The signed Pauli string `(-1)^(s_j) P_j` of a table entry `(s_j, row)`. -/
noncomputable def selectPauliTerm {N : ℕ} (t : Bool × (Fin N → Pauli)) : Unitary (2 ^ N) :=
  selectPauliSign N t.1 * selectPauliString t.2

/-- Data basis index of index value `j` and system basis index `x`: `(j, x) ↦ x + 2^N * j`, so the
system occupies the `N` least significant bits (the first `N` data wires) and the index register
the next `b` bits. -/
def selectPauliDataEquiv (b N : ℕ) : Fin (2 ^ b) × Fin (2 ^ N) ≃ Fin (2 ^ (N + b)) :=
  finProdFinEquiv.trans (finCongr (by rw [pow_add, mul_comm]))

theorem selectPauliDataEquiv_val (b N : ℕ) (j : Fin (2 ^ b)) (x : Fin (2 ^ N)) :
    (selectPauliDataEquiv b N (j, x)).val = x.val + 2 ^ N * j.val := rfl

/-- Block-diagonal unitary `∑_k |k⟩⟨k| ⊗ B k`, reindexed to `Fin d` by `e`. -/
noncomputable def selectPauliBlockDiagonal {m o : Type} [Fintype m] [DecidableEq m] [Fintype o]
    [DecidableEq o] {d : ℕ} (e : m × o ≃ Fin d) (B : o → 𝐔[m]) : Unitary d :=
  ⟨(blockDiagonal fun k ↦ (B k).1).submatrix e.symm e.symm, by
    have hB : ∀ k, (B k).1 * ((B k).1)ᴴ = 1 := fun k ↦ by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff.mp (B k).2
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
    simp only [hB]
    rw [← Pi.one_def, blockDiagonal_one, Matrix.submatrix_one_equiv]⟩

/-- The system operation selected by index value `j`: the signed string `(-1)^(s_j) P_j` for
`j < L`, the identity otherwise. `selectPauli_correctness` uses it with `L = 2^b`, where every
index value has a row. -/
noncomputable def selectPauliBlock (b N L : ℕ) (tbl : SelectPauliTable L N) (j : Fin (2 ^ b)) :
    Unitary (2 ^ N) :=
  if h : j.val < L then selectPauliTerm (tbl ⟨j.val, h⟩) else 1

/-- Ideal `SELECT` unitary on the `N + b` data qubits:
`|x⟩|j⟩ ↦ (-1)^(s_j) (P_j |x⟩)|j⟩` for `j < L` (and `|x⟩|j⟩ ↦ |x⟩|j⟩` for `j ≥ L`), in the
encoding `selectPauliDataEquiv`. -/
noncomputable def selectPauliUnitary (b N L : ℕ) (tbl : SelectPauliTable L N) :
    Unitary (2 ^ (N + b)) :=
  selectPauliBlockDiagonal ((Equiv.prodComm _ _).trans (selectPauliDataEquiv b N))
    (selectPauliBlock b N L tbl)

/-- Sanity check: on a basis state with index `j < L`, `selectPauliUnitary` keeps the index and
applies the signed string to the system,
`|x⟩|j⟩ ↦ (∑_y ((-1)^(s_j) P_j)_{y x} |y⟩) ⊗ |j⟩`. -/
theorem selectPauliUnitary_mulVec_basisState (b N L : ℕ) (tbl : SelectPauliTable L N)
    (j : Fin (2 ^ b)) (hj : j.val < L) (x : Fin (2 ^ N)) :
    (selectPauliUnitary b N L tbl).1 *ᵥ basisState (selectPauliDataEquiv b N (j, x)) =
      ∑ y : Fin (2 ^ N), (selectPauliTerm (tbl ⟨j.val, hj⟩)).1 y x •
        basisState (selectPauliDataEquiv b N (j, y)) := by
  ext d
  obtain ⟨⟨j', y'⟩, rfl⟩ := (selectPauliDataEquiv b N).surjective d
  simp only [basisState, Matrix.mulVec_single_one]
  by_cases hj' : j' = j
  · subst hj'
    simp [selectPauliUnitary, selectPauliBlockDiagonal, selectPauliBlock, hj, Pi.single_apply,
      Finset.sum_apply]
  · simp [selectPauliUnitary, selectPauliBlockDiagonal, hj', Finset.sum_apply,
      blockDiagonal_apply']

/-- Sanity check: the one-qubit string `Y` maps `|0⟩` to `i |1⟩`. -/
theorem selectPauliString_Y_mulVec_zero :
    (selectPauliString (fun _ : Fin 1 ↦ Pauli.Y)).1 *ᵥ basisState 0 =
      Complex.I • basisState 1 := by
  simp only [selectPauliString, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    mul_one, QRegister.singleton_eq_whole, QRegister.whole_embedUnitary, SelectPauli.Pauli.unitary,
    basisState, Matrix.mulVec_single_one]
  ext i
  fin_cases i <;> simp [Qubit.Y]

/-- Sanity check: the one-qubit term with sign bit `true` and row `I` maps `|0⟩` to `-|0⟩`. -/
theorem selectPauliTerm_neg_I_mulVec_zero :
    (selectPauliTerm (true, fun _ : Fin 1 ↦ Pauli.I)).1 *ᵥ basisState 0 = -basisState 0 := by
  have h : (selectPauliTerm (true, fun _ : Fin 1 ↦ Pauli.I)).1 = -1 := by
    simp [selectPauliTerm, selectPauliSign, selectPauliString, List.ofFn_succ,
      QRegister.singleton_eq_whole, SelectPauli.Pauli.unitary]
  rw [h, Matrix.neg_mulVec, Matrix.one_mulVec]

/-- `tbl'` completes the table `tbl` to all `2^b` index values: it has the same row as `tbl` for
every `j < L`. Its rows for `j ≥ L` are not constrained. -/
def SelectPauliCompletes (b N L : ℕ) (tbl : SelectPauliTable L N)
    (tbl' : SelectPauliTable (2 ^ b) N) : Prop :=
  ∀ (j : Fin L) (h : j.val < 2 ^ b), tbl' ⟨j.val, h⟩ = tbl j

set_option maxRecDepth 20000 in
/-- Wire pinning: for `N = b = 1` and `L = 2` with term `0` equal to `+I` and term `1` equal to
`+X`, the ideal unitary is the library's `CNOT` with control on data wire `1` (the index) and
target on data wire `0` (the system), where `CNOT` has the library's gate semantics
(`PrimitiveGate.cnotUnitary`, via `Circuit.eval`). This fixes the wire order, the bit order and
the sign convention of the whole statement. -/
theorem selectPauli_pins_cnot (tbl : SelectPauliTable 2 1)
    (h0 : tbl 0 = (false, fun _ ↦ Pauli.I)) (h1 : tbl 1 = (false, fun _ ↦ Pauli.X)) :
    selectPauliUnitary 1 1 2 tbl = (Circuit.CNOT (1 : Fin 2) 0 (by decide)).eval := by
  have hemp : IsEmpty (QRegister.pair (1 : Fin 2) 0 (by decide)).Environment :=
    ⟨fun ⟨q, hq⟩ ↦ by
      fin_cases q
      · exact hq ⟨1, rfl⟩
      · exact hq ⟨0, rfl⟩⟩
  have hext : ∀ i : Fin 4, (QRegister.pair (1 : Fin 2) 0 (by decide)).extractIndex i =
      ![0, 2, 1, 3] i := by
    decide
  have hentry : ∀ i k : Fin 4, (Circuit.CNOT (1 : Fin 2) 0 (by decide)).eval.1 i k =
      PrimitiveGate.cnotUnitary.1 (![0, 2, 1, 3] i) (![0, 2, 1, 3] k) := by
    intro i k
    change (QRegister.pair (1 : Fin 2) 0 (by decide)).embedMatrix PrimitiveGate.cnotUnitary.1 i k = _
    have hc : ((QRegister.pair (1 : Fin 2) 0 (by decide)).basisSplitEquiv i).2 =
        ((QRegister.pair (1 : Fin 2) 0 (by decide)).basisSplitEquiv k).2 := Subsingleton.elim _ _
    rw [QRegister.embedMatrix_apply, hext, hext]
    simp [hc]
  have hE : ∀ (j : Fin (2 ^ 1)) (x : Fin (2 ^ 1)), selectPauliDataEquiv 1 1 (j, x) =
      ⟨x.val + 2 * j.val, by have := j.2; have := x.2; omega⟩ := fun j x ↦
    Fin.ext (selectPauliDataEquiv_val 1 1 j x)
  have t1 : ∀ h : 1 < 2, tbl ⟨1, h⟩ = (false, fun _ ↦ Pauli.X) := fun _ ↦ h1
  have hL := selectPauliUnitary_mulVec_basisState 1 1 2 tbl
  apply Subtype.ext
  ext i k
  rw [hentry]
  obtain ⟨⟨j', y'⟩, rfl⟩ := (selectPauliDataEquiv 1 1).surjective i
  obtain ⟨⟨j, x⟩, rfl⟩ := (selectPauliDataEquiv 1 1).surjective k
  have hj : j.val < 2 := by simpa using j.isLt
  have hcol := congrFun (hL j hj x) (selectPauliDataEquiv 1 1 (j', y'))
  have hU : (selectPauliUnitary 1 1 2 tbl).1 (selectPauliDataEquiv 1 1 (j', y'))
      (selectPauliDataEquiv 1 1 (j, x)) =
      ∑ y : Fin (2 ^ 1), (selectPauliTerm (tbl ⟨j.val, hj⟩)).1 y x *
        basisState (selectPauliDataEquiv 1 1 (j, y)) (selectPauliDataEquiv 1 1 (j', y')) := by
    simpa [basisState, Matrix.mulVec_single_one, Finset.sum_apply] using hcol
  rw [hU]
  have hcn : ∀ a b : Fin 4, PrimitiveGate.cnotUnitary.1 a b =
      if Equiv.swap (1 : Fin 4) 3 a = b then 1 else 0 := by
    intro a b
    simp [PrimitiveGate.cnotUnitary, permutationUnitary, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Equiv.swap_inv]
  rw [hcn]
  have hs : ∀ f : Fin (2 ^ 1) → ℂ, ∑ y, f y = f 0 + f 1 := fun f ↦ Fin.sum_univ_two f
  fin_cases j <;> fin_cases x <;> fin_cases j' <;> fin_cases y'
  all_goals
    simp only [hs, Fin.zero_eta, Fin.isValue, Fin.val_zero, t1, hE]
  all_goals
    simp [h0, selectPauliTerm, selectPauliSign, selectPauliString, List.ofFn_succ,
      QRegister.singleton_eq_whole, QRegister.whole_embedUnitary, SelectPauli.Pauli.unitary,
      Qubit.X, basisState, Fin.ext_iff, Equiv.swap_apply_def]

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive SelectPauli.Var where | v deriving DecidableEq, Inhabited

open SelectPauli (Var)
open SelectPauli.Var (v)

namespace SelectPauliBridge

open Operator Matrix QProg Function SelectPauliSteps HermitianMat
open scoped Matrix ComplexOrder MatrixOrder

theorem bits_zero_of_localIdx_eq_zero {m n : ℕ} (r : QRegister m n) (β : BitAssignment n)
    (h : localIdx r β = 0) (i : Fin m) : β (r i) = 0 := by
  have h' : (fun i ↦ β (r i)) = basisBits m 0 := by
    rw [← h]
    simp [localIdx]
  have := congrFun h' i
  rw [this, basisBits_eq_div_mod]
  simp


end SelectPauliBridge


/-! ### General bridge for `RealizesCleanSubroutine`

From a Kraus lower bound `R` of `P` whose action on every clean basis ket is that of the embedded
unitary `U`, conclude `RealizesCleanSubroutine`. Not specific to `SELECT`; stated for any
registers, any `U`. The final step is Google's `SelectPauliSteps.realizesCleanSubroutine_of_lowerKraus`
(Arcsin solution), which needs the matrix identity `Π₀ R = Π₀ E Π₀`. The new content is that this
identity follows from the ket-level statement plus the contraction bound `Rᴴ R ≤ 1` that
`LowerKraus` carries: `R` is isometric on the clean subspace, hence maps its orthogonal
complement into the orthogonal complement of the image `E`(clean) = clean. -/
namespace CleanSubroutineBridge

open Operator Matrix QProg Function SelectPauliSteps HermitianMat
open scoped Matrix ComplexOrder MatrixOrder

/-- An embedded unitary on a register disjoint from `rA` commutes with the clean projector of
`rA`. -/
theorem embed_comm_proj {k m n : ℕ} (rT : QRegister k n) (rA : QRegister m n)
    (hd : rT.DisjointWires rA) (U : Unitary (2 ^ k)) :
    rA.basisOutcomeProjector 0 * (rT.embedUnitary U).1 =
      (rT.embedUnitary U).1 * rA.basisOutcomeProjector 0 := by
  apply matrix_ext_ket
  intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, basisOutcomeProjector_mulVec_ket,
    QRegister.embedUnitary_val, embedMatrix_mulVec_ket]
  by_cases h0 : localIdx rA β = 0
  · rw [if_pos h0, embedMatrix_mulVec_ket, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, basisOutcomeProjector_mulVec_ket,
      localIdx_writeReg_of_disjoint β rT rA hd, h0, if_true]
  · rw [if_neg h0, Matrix.mulVec_zero]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, basisOutcomeProjector_mulVec_ket,
      localIdx_writeReg_of_disjoint β rT rA hd, h0, if_false, smul_zero,
      Finset.sum_const_zero]

/-- Main bridge. If `R` is a Kraus lower bound of `P` (`LowerKraus P R`) and `R` agrees with the
embedded unitary `rT.embedUnitary U` on every basis ket whose `rA` bits are all zero, then `P`
realizes `U` on `rT` as a clean subroutine with ancillas `rA`. -/
theorem realizesCleanSubroutine_of_lowerKraus_ket {Var : Type} [DecidableEq Var] {n k m : ℕ}
    [NeZero (2 ^ n)] (rT : QRegister k n) (rA : QRegister m n) (hd : rT.DisjointWires rA)
    (U : Unitary (2 ^ k)) {P : QProg Var (2 ^ n)}
    {R : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (hP : LowerKraus P R)
    (hkey : ∀ β, localIdx rA β = 0 → R *ᵥ ket β = (rT.embedUnitary U).1 *ᵥ ket β) :
    RealizesCleanSubroutine rT rA hd U P := by
  set Q0 := rA.basisOutcomeProjector 0 with hQ
  set E := (rT.embedUnitary U).1 with hE
  have hcomm : Q0 * E = E * Q0 := embed_comm_proj rT rA hd U
  have hQh : Q0ᴴ = Q0 := QRegister.basisOutcomeProjector_conjTranspose _ _
  have hQQ : Q0 * Q0 = Q0 := QRegister.basisOutcomeProjector_mul_self _ _
  have hEE : Eᴴ * E = 1 := by
    have h := Unitary.coe_star_mul_self (rT.embedUnitary U)
    rw [Matrix.star_eq_conjTranspose] at h
    exact h
  have hEE' : E * Eᴴ = 1 := by
    have h := Unitary.coe_mul_star_self (rT.embedUnitary U)
    rw [Unitary.coe_star, Matrix.star_eq_conjTranspose] at h
    exact h
  -- `R` and `E` agree on the clean subspace
  have hRQ : R * Q0 = E * Q0 := by
    apply matrix_ext_ket
    intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQ, basisOutcomeProjector_mulVec_ket]
    by_cases h0 : localIdx rA β = 0
    · rw [if_pos h0]; exact hkey β h0
    · rw [if_neg h0, Matrix.mulVec_zero, Matrix.mulVec_zero]
  -- `R` is isometric on the clean subspace
  have hiso : Q0 * (Rᴴ * R) * Q0 = Q0 := by
    have h1 : (R * Q0)ᴴ * (R * Q0) = (E * Q0)ᴴ * (E * Q0) := by rw [hRQ]
    simp only [Matrix.conjTranspose_mul, hQh] at h1
    calc Q0 * (Rᴴ * R) * Q0 = Q0 * (Rᴴ * (R * Q0)) := by simp only [Matrix.mul_assoc]
      _ = Q0 * (Eᴴ * (E * Q0)) := by simpa only [Matrix.mul_assoc] using h1
      _ = Q0 := by rw [← Matrix.mul_assoc Eᴴ, hEE, Matrix.one_mul, hQQ]
  -- `1 - Rᴴ R` is positive semidefinite
  have hpsd : (1 - Rᴴ * R).PosSemidef := by
    have h := hP.conj_le_one 1
    have := (HermitianMat.le_iff.mp h)
    simpa [HermitianMat.conj_apply_mat, Matrix.mul_assoc] using this
  have hzero : Q0ᴴ * ((1 - Rᴴ * R) * Q0) = 0 := by
    rw [hQh, ← Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hiso, hQQ,
      sub_self]
  have hDQ : (1 - Rᴴ * R) * Q0 = 0 := by
    apply matrix_ext_ket
    intro β
    rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
    set y := Q0 *ᵥ ket β with hy
    refine (hpsd.dotProduct_mulVec_zero_iff).mp ?_
    have h3 : star y ⬝ᵥ ((1 - Rᴴ * R) *ᵥ y) = star (ket β) ⬝ᵥ ((Q0ᴴ * ((1 - Rᴴ * R) * Q0)) *ᵥ ket β) := by
      rw [hy, Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
      simp only [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
        Matrix.mul_assoc]
    rw [h3, hzero, Matrix.zero_mulVec, dotProduct_zero]
  have hRRQ : Rᴴ * R * Q0 = Q0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hDQ
    exact hDQ.symm
  -- `Q0 = E Q0 Eᴴ`
  have hQE : E * Q0 * Eᴴ = Q0 := by
    rw [← hcomm, Matrix.mul_assoc, hEE', Matrix.mul_one]
  have hcomm' : Q0 * Eᴴ = Eᴴ * Q0 := by
    have := congrArg Matrix.conjTranspose hcomm
    simpa [Matrix.conjTranspose_mul, hQh] using this.symm
  -- `Rᴴ Q0 = Q0 Eᴴ`, hence `Q0 R = E Q0`
  have hRH : Rᴴ * Q0 = Q0 * Eᴴ := by
    calc Rᴴ * Q0 = Rᴴ * (E * Q0 * Eᴴ) := by rw [hQE]
      _ = Rᴴ * (R * Q0) * Eᴴ := by rw [← hRQ, ← Matrix.mul_assoc]
      _ = (Rᴴ * R * Q0) * Eᴴ := by simp only [Matrix.mul_assoc]
      _ = Q0 * Eᴴ := by rw [hRRQ]
  have hR : Q0 * R = Q0 * E * Q0 := by
    have := congrArg Matrix.conjTranspose hRH
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hQh] at this
    rw [this, Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc, hQQ]
  exact realizesCleanSubroutine_of_lowerKraus rT rA hd U hP hR

end CleanSubroutineBridge

namespace SelectPauliImpl

open Operator Matrix QProg Function SelectPauliSteps
open scoped Matrix ComplexOrder MatrixOrder

/-- Bit flipped by the Pauli. -/
def pf : Pauli → ZMod 2
  | .I => 0
  | .X => 1
  | .Y => 1
  | .Z => 0

/-- Phase picked up by the Pauli on a basis ket with bit `x`. -/
noncomputable def pc : Pauli → ZMod 2 → ℂ
  | .I, _ => 1
  | .X, _ => 1
  | .Y, x => if x = 0 then Complex.I else -Complex.I
  | .Z, x => bitSign x

theorem pauli_ket {N : ℕ} (q : Wire N) (p : Pauli) (δ : BitAssignment N) :
    ((QRegister.singleton q).embedUnitary p.unitary).1.mulVec (ket δ) =
      pc p (δ q) • ket (update δ q (δ q + pf p)) := by
  rw [QRegister.embedUnitary_val]
  have e := Function.update_eq_self q δ
  cases p
  · show ((QRegister.singleton q).embedMatrix (1 : Matrix (Fin 2) (Fin 2) ℂ)).mulVec _ = _
    rw [singleton_embedMatrix_mulVec_ket]
    rcases bit_cases (δ q) with h | h <;> rw [h] at e <;>
      simp [h, e, pf, pc, Matrix.one_apply]
  · show ((QRegister.singleton q).embedMatrix !![(0 : ℂ), 1; 1, 0]).mulVec _ = _
    rw [singleton_embedMatrix_mulVec_ket]
    rcases bit_cases (δ q) with h | h <;> rw [h] at e <;>
      simp [h, e, pf, pc, one_add_one_zmod2]
  · show ((QRegister.singleton q).embedMatrix !![(0 : ℂ), -Complex.I; Complex.I, 0]).mulVec _ = _
    rw [singleton_embedMatrix_mulVec_ket]
    rcases bit_cases (δ q) with h | h <;> rw [h] at e <;>
      simp [h, e, pf, pc, one_add_one_zmod2]
  · show ((QRegister.singleton q).embedMatrix !![(1 : ℂ), 0; 0, -1]).mulVec _ = _
    rw [singleton_embedMatrix_mulVec_ket]
    rcases bit_cases (δ q) with h | h <;> rw [h] at e <;>
      simp [h, e, pf, pc, one_add_one_zmod2, bitSign]


theorem update_eq_add_single {n : ℕ} (β : BitAssignment n) (w : Wire n) (a : ZMod 2) :
    update β w (β w + a) = β + Pi.single w a := by
  funext x
  by_cases h : x = w
  · subst h; simp
  · simp [h, Pi.single_apply]

theorem unitary_list_prod_ket {N : ℕ} (row : Fin N → Pauli) (l : List (Fin N)) (hl : l.Nodup)
    (δ : BitAssignment N) :
    (l.map fun q : Fin N ↦ (QRegister.singleton q).embedUnitary (row q).unitary).prod.1.mulVec
        (ket δ) =
      (l.map fun q ↦ pc (row q) (δ q)).prod •
        ket (δ + ∑ q ∈ l.toFinset, Pi.single q (pf (row q))) := by
  induction l generalizing δ with
  | nil =>
    have h1 : ((1 : Unitary (2 ^ N)).1) = 1 := rfl
    simp only [List.map_nil, List.prod_nil, List.toFinset_nil, Finset.sum_empty, add_zero,
      one_smul, h1, Matrix.one_mulVec]
  | cons q l ih =>
    rw [List.nodup_cons] at hl
    have hq : q ∉ l.toFinset := by simpa using hl.1
    have h0 : (δ + ∑ q' ∈ l.toFinset, Pi.single q' (pf (row q'))) q = δ q := by
      simp only [Pi.add_apply, Finset.sum_apply, Pi.single_apply]
      rw [Finset.sum_eq_zero]
      · simp
      · intro q' hq'
        have : q ≠ q' := fun h ↦ hq (h ▸ hq')
        simp [this]
    have hu := update_eq_add_single (δ + ∑ q' ∈ l.toFinset, Pi.single q' (pf (row q'))) q
      (pf (row q))
    rw [h0] at hu
    rw [List.map_cons, List.prod_cons, show ∀ (a b : Unitary (2 ^ N)), (a * b).1 = a.1 * b.1
      from fun _ _ ↦ rfl, ← Matrix.mulVec_mulVec, ih hl.2 δ, Matrix.mulVec_smul, pauli_ket, h0, hu,
      smul_smul, List.map_cons, List.prod_cons, List.toFinset_cons, Finset.sum_insert hq]
    have : δ + ∑ q' ∈ l.toFinset, Pi.single q' (pf (row q')) + Pi.single q (pf (row q)) =
        δ + (Pi.single q (pf (row q)) + ∑ q' ∈ l.toFinset, Pi.single q' (pf (row q'))) := by
      abel
    rw [this, mul_comm]

/-- Controlled Pauli: apply `p` to `t` when `c` is set. -/
def ctrlPauli {n : ℕ} (c t : Wire n) (h : c ≠ t) : Pauli → Circuit n
  | .I => .identity
  | .X => Circuit.CNOT c t h
  | .Y => .seq (.seq (Circuit.Z t) (Circuit.S t)) (.seq (Circuit.CNOT c t h) (Circuit.S t))
  | .Z => fixupCZ c t

theorem ctrlPauli_ket0 {n : ℕ} (c t : Wire n) (h : c ≠ t) (p : Pauli) (β : BitAssignment n)
    (hc : β c = 0) :
    (ctrlPauli c t h p).eval.1.mulVec (ket β) = ket β := by
  have e := Function.update_eq_self t β
  cases p
  · rw [ctrlPauli, Circuit.eval_identity]
    exact Matrix.one_mulVec _
  · rw [ctrlPauli, ket_CNOT, hc, add_zero, e]
  · simp only [ctrlPauli, eval_seq_mulVec, ket_Z, ket_S, ket_CNOT, Matrix.mulVec_smul, smul_smul,
      update_self, hc, add_zero, e]
    rcases bit_cases (β t) with ht | ht <;> simp [ht, bitSign, bitPhaseI]
  · rw [ctrlPauli, fixupCZ_mulVec_ket c t h, hc]
    simp [bitSign]

theorem ctrlPauli_ket1 {n : ℕ} (c t : Wire n) (h : c ≠ t) (p : Pauli) (β : BitAssignment n)
    (hc : β c = 1) :
    (ctrlPauli c t h p).eval.1.mulVec (ket β) = pc p (β t) • ket (update β t (β t + pf p)) := by
  have e := Function.update_eq_self t β
  cases p
  · rw [ctrlPauli, Circuit.eval_identity]
    simp only [pf, pc, add_zero, e, one_smul]
    exact Matrix.one_mulVec _
  · rw [ctrlPauli, ket_CNOT, hc]
    simp [pf, pc]
  · simp only [ctrlPauli, eval_seq_mulVec, ket_Z, ket_S, ket_CNOT, Matrix.mulVec_smul, smul_smul,
      update_self, hc, e]
    rcases bit_cases (β t) with ht | ht <;>
      simp [ht, bitSign, bitPhaseI, pc, pf, one_add_one_zmod2]
  · rw [ctrlPauli, fixupCZ_mulVec_ket c t h, hc]
    simp [pf, pc, e]

def ctrlStr {N n : ℕ} (c : Wire n) (sw : Fin N → Wire n) (hsw : ∀ q, c ≠ sw q)
    (row : Fin N → Pauli) : Circuit n :=
  Circuit.sequence ((List.finRange N).map fun q ↦ ctrlPauli c (sw q) (hsw q) (row q))

theorem ctrlList_ket0 {N n : ℕ} (c : Wire n) (sw : Fin N → Wire n) (hsw : ∀ q, c ≠ sw q)
    (row : Fin N → Pauli) (l : List (Fin N)) (β : BitAssignment n) (hc : β c = 0) :
    (Circuit.sequence (l.map fun q ↦ ctrlPauli c (sw q) (hsw q) (row q))).eval.1.mulVec (ket β) =
      ket β := by
  induction l with
  | nil =>
    rw [List.map_nil, Circuit.sequence_nil, Circuit.eval_identity]
    exact Matrix.one_mulVec _
  | cons q l ih =>
    simp only [List.map_cons, Circuit.sequence_cons, eval_seq_mulVec,
      ctrlPauli_ket0 _ _ _ _ _ hc, ih]

theorem ctrlList_ket1 {N n : ℕ} (c : Wire n) (sw : Fin N → Wire n) (hsw : ∀ q, c ≠ sw q)
    (hinj : Function.Injective sw) (row : Fin N → Pauli) (l : List (Fin N)) (hl : l.Nodup)
    (β : BitAssignment n) (hc : β c = 1) :
    (Circuit.sequence (l.map fun q ↦ ctrlPauli c (sw q) (hsw q) (row q))).eval.1.mulVec (ket β) =
      (l.map fun q ↦ pc (row q) (β (sw q))).prod •
        ket (β + ∑ q ∈ l.toFinset, Pi.single (sw q) (pf (row q))) := by
  induction l generalizing β with
  | nil =>
    rw [List.map_nil, Circuit.sequence_nil, Circuit.eval_identity]
    simp only [List.map_nil, List.prod_nil, List.toFinset_nil, Finset.sum_empty, add_zero, one_smul]
    exact Matrix.one_mulVec _
  | cons q l ih =>
    rw [List.nodup_cons] at hl
    have hq : q ∉ l.toFinset := by simpa using hl.1
    have hβ' := update_eq_add_single β (sw q) (pf (row q))
    have hc' : (β + (Pi.single (sw q) (pf (row q)) : BitAssignment n)) c = 1 := by
      simp [hc, Pi.single_apply, hsw q]
    have hph : (l.map fun q' ↦ pc (row q') ((β + (Pi.single (sw q) (pf (row q)) : BitAssignment n)) (sw q'))) =
        l.map fun q' ↦ pc (row q') (β (sw q')) := by
      refine List.map_congr_left fun q' hq' ↦ ?_
      have hne : sw q' ≠ sw q := fun h ↦ hl.1 (hinj h ▸ hq')
      simp [Pi.single_apply, hne]
    rw [List.map_cons, Circuit.sequence_cons, eval_seq_mulVec, ctrlPauli_ket1 _ _ _ _ _ hc,
      Matrix.mulVec_smul, hβ', ih hl.2 _ hc', hph, smul_smul, List.map_cons, List.prod_cons,
      List.toFinset_cons, Finset.sum_insert hq]
    have : β + Pi.single (sw q) (pf (row q)) + ∑ q' ∈ l.toFinset, Pi.single (sw q') (pf (row q')) =
        β + (Pi.single (sw q) (pf (row q)) + ∑ q' ∈ l.toFinset, Pi.single (sw q') (pf (row q'))) := by
      abel
    rw [this]


theorem id_mulVec {n : ℕ} (v : Fin (2 ^ n) → ℂ) :
    (Circuit.identity : Circuit n).eval.1.mulVec v = v := Matrix.one_mulVec v

theorem inv_mulVec {n : ℕ} (c : Circuit n) (v : Fin (2 ^ n) → ℂ) :
    c.inverse.eval.1.mulVec (c.eval.1.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, Circuit.eval_inverse]
  have : ((c.eval⁻¹ * c.eval : Unitary (2 ^ n))).1 = 1 := by rw [inv_mul_cancel]; rfl
  rw [show (c.eval⁻¹).1 * c.eval.1 = ((c.eval⁻¹ * c.eval : Unitary (2 ^ n))).1 from rfl, this,
    Matrix.one_mulVec]

/-- Wires of a placement: system wires, index wires, and the `b + 1` ancilla chain. -/
structure Wires (b N n : ℕ) where
  sw : Fin N → Wire n
  xw : Fin b → Wire n
  aw : Fin (b + 1) → Wire n
  sw_inj : Function.Injective sw
  xw_inj : Function.Injective xw
  aw_inj : Function.Injective aw
  sx : ∀ q i, sw q ≠ xw i
  sa : ∀ q k, sw q ≠ aw k
  xa : ∀ i k, xw i ≠ aw k

namespace Wires

variable {b N n : ℕ} (W : Wires b N n)

def andStep (i : Fin b) : Circuit n :=
  AND4T (W.aw i.castSucc) (W.xw i) (W.aw i.succ) (W.xa i _).symm
    (fun h ↦ (Fin.castSucc_lt_succ : Fin.castSucc i < Fin.succ i).ne (W.aw_inj h)) (W.xa i _)

def xlayer (jb : Fin b → ZMod 2) : Circuit n :=
  Circuit.sequence ((List.finRange b).map fun i ↦
    if jb i = 0 then Circuit.X (W.xw i) else Circuit.identity)

def chainN : ℕ → Circuit n
  | 0 => .identity
  | k + 1 => .seq (chainN k) (if h : k < b then W.andStep ⟨k, h⟩ else .identity)

def wcirc (jb : Fin b → ZMod 2) : Circuit n :=
  .seq (Circuit.X (W.aw 0)) (.seq (W.xlayer jb) (W.chainN b))

def xp (jb : Fin b → ZMod 2) (β : BitAssignment n) (i : ℕ) : ZMod 2 :=
  if h : i < b then β (W.xw ⟨i, h⟩) + (1 + jb ⟨i, h⟩) else 0

def aval (jb : Fin b → ZMod 2) (β : BitAssignment n) : ℕ → ZMod 2
  | 0 => 1
  | k + 1 => aval jb β k * W.xp jb β k

/-- Invariant of the chain after `k` AND steps, starting from the clean state `β`. -/
def Inv (jb : Fin b → ZMod 2) (β : BitAssignment n) (k : ℕ) (γ : BitAssignment n) : Prop :=
  (∀ i : Fin (b + 1), γ (W.aw i) = if i.val ≤ k then W.aval jb β i.val else 0) ∧
  (∀ i : Fin b, γ (W.xw i) = β (W.xw i) + (1 + jb i)) ∧
  (∀ w, (∀ i, w ≠ W.aw i) → (∀ i, w ≠ W.xw i) → γ w = β w)

theorem Inv_ext {jb : Fin b → ZMod 2} {β : BitAssignment n} {k : ℕ} {γ γ' : BitAssignment n}
    (h : W.Inv jb β k γ) (h' : W.Inv jb β k γ') : γ = γ' := by
  funext w
  by_cases ha : ∃ i, w = W.aw i
  · obtain ⟨i, rfl⟩ := ha
    rw [h.1 i, h'.1 i]
  by_cases hx : ∃ i, w = W.xw i
  · obtain ⟨i, rfl⟩ := hx
    rw [h.2.1 i, h'.2.1 i]
  simp only [not_exists] at ha hx
  rw [h.2.2 w ha hx, h'.2.2 w ha hx]

theorem xp_shift (jb : Fin b → ZMod 2) (β s : BitAssignment n) (hs : ∀ i, s (W.xw i) = 0)
    (i : ℕ) : W.xp jb (β + s) i = W.xp jb β i := by
  unfold xp
  split_ifs with h
  · simp [hs]
  · rfl

theorem aval_shift (jb : Fin b → ZMod 2) (β s : BitAssignment n) (hs : ∀ i, s (W.xw i) = 0)
    (k : ℕ) : W.aval jb (β + s) k = W.aval jb β k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [aval, ih, xp_shift W jb β s hs]

theorem Inv_shift {jb : Fin b → ZMod 2} {β : BitAssignment n} {k : ℕ} {γ : BitAssignment n}
    (h : W.Inv jb β k γ) (s : BitAssignment n) (hx : ∀ i, s (W.xw i) = 0)
    (ha : ∀ i, s (W.aw i) = 0) : W.Inv jb (β + s) k (γ + s) := by
  refine ⟨fun i ↦ ?_, fun i ↦ ?_, fun w hw1 hw2 ↦ ?_⟩
  · simp [h.1 i, ha, aval_shift W jb β s hx]
  · simp [h.2.1 i, hx, add_assoc]
  · simp [h.2.2 w hw1 hw2]

theorem xl_ket (jb : Fin b → ZMod 2) (l : List (Fin b)) (β : BitAssignment n) :
    (Circuit.sequence (l.map fun i ↦
      if jb i = 0 then Circuit.X (W.xw i) else Circuit.identity)).eval.1.mulVec (ket β) =
      ket (β + (l.map fun i ↦ if jb i = 0 then Pi.single (W.xw i) (1 : ZMod 2) else 0).sum) := by
  induction l generalizing β with
  | nil =>
    rw [List.map_nil, Circuit.sequence_nil, Circuit.eval_identity]
    simp only [List.map_nil, List.sum_nil, add_zero]
    exact Matrix.one_mulVec _
  | cons i l ih =>
    by_cases h : jb i = 0
    · simp only [List.map_cons, Circuit.sequence_cons, eval_seq_mulVec, List.sum_cons, h, if_true]
      rw [ket_X, update_eq_add_single, ih, add_assoc]
    · simp only [List.map_cons, Circuit.sequence_cons, eval_seq_mulVec, List.sum_cons, h, if_false]
      rw [id_mulVec, ih, zero_add]

theorem xsum_xw (jb : Fin b → ZMod 2) (i : Fin b) :
    (∑ i' : Fin b, if jb i' = 0 then (Pi.single (W.xw i') (1 : ZMod 2) : BitAssignment n) else 0) (W.xw i) =
      if jb i = 0 then 1 else 0 := by
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · split_ifs <;> simp
  · intro i' _ hne
    split_ifs
    · simp [Pi.single_apply, W.xw_inj.eq_iff, Ne.symm hne]
    · rfl
  · simp

theorem xsum_other (jb : Fin b → ZMod 2) (w : Wire n) (hw : ∀ i, w ≠ W.xw i) :
    (∑ i' : Fin b, if jb i' = 0 then (Pi.single (W.xw i') (1 : ZMod 2) : BitAssignment n) else 0) w = 0 := by
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun i' _ ↦ ?_
  split_ifs
  · simp [Pi.single_apply, hw i']
  · rfl

theorem chain_ket (jb : Fin b → ZMod 2) (β γ0 : BitAssignment n) (h0 : W.Inv jb β 0 γ0) :
    ∀ k, k ≤ b → ∃ γ, W.Inv jb β k γ ∧ (W.chainN k).eval.1.mulVec (ket γ0) = ket γ := by
  intro k
  induction k with
  | zero => intro _; exact ⟨γ0, h0, id_mulVec _⟩
  | succ k ih =>
    intro hk
    obtain ⟨γ, hγ, hket⟩ := ih (by omega)
    have hk' : k < b := by omega
    have e1 : γ (W.aw (Fin.castSucc ⟨k, hk'⟩)) = W.aval jb β k := by
      have := hγ.1 (Fin.castSucc ⟨k, hk'⟩); simpa using this
    have e2 : γ (W.xw ⟨k, hk'⟩) = W.xp jb β k := by
      rw [hγ.2.1]; simp [xp, hk']
    have e3 : γ (W.aw (Fin.succ ⟨k, hk'⟩)) = 0 := by
      have := hγ.1 (Fin.succ ⟨k, hk'⟩); simpa using this
    refine ⟨Function.update γ (W.aw (Fin.succ ⟨k, hk'⟩)) (W.aval jb β (k + 1)), ?_, ?_⟩
    · refine ⟨fun i ↦ ?_, fun i ↦ ?_, fun w hw1 hw2 ↦ ?_⟩
      · by_cases hi : i = Fin.succ ⟨k, hk'⟩
        · subst hi; simp
        · have hne : W.aw i ≠ W.aw (Fin.succ ⟨k, hk'⟩) := fun h ↦ hi (W.aw_inj h)
          have hv : i.val ≠ k + 1 := fun h ↦ hi (Fin.ext (by simpa using h))
          rw [Function.update_of_ne hne, hγ.1 i]
          by_cases hik : i.val ≤ k
          · simp [hik, show i.val ≤ k + 1 by omega]
          · simp [hik, show ¬ i.val ≤ k + 1 by omega]
      · rw [Function.update_of_ne (W.xa i _), hγ.2.1 i]
      · rw [Function.update_of_ne (hw1 _), hγ.2.2 w hw1 hw2]
    · simp only [chainN, dif_pos hk', eval_seq_mulVec, hket, andStep]
      rw [ket_AND4T_eq_smul, e1, e2, e3]
      simp only [cleanAndPhase, if_true, one_smul, zero_add]
      rfl

theorem wcirc_ket (jb : Fin b → ZMod 2) (β : BitAssignment n) (hc : ∀ k, β (W.aw k) = 0) :
    ∃ γ, W.Inv jb β b γ ∧ (W.wcirc jb).eval.1.mulVec (ket β) = ket γ := by
  set xs : BitAssignment n :=
    ∑ i' : Fin b, if jb i' = 0 then (Pi.single (W.xw i') (1 : ZMod 2) : BitAssignment n) else 0 with hxs
  have hinv0 : W.Inv jb β 0 (β + Pi.single (W.aw 0) 1 + xs) := by
    refine ⟨fun i ↦ ?_, fun i ↦ ?_, fun w hw1 hw2 ↦ ?_⟩
    · have hx : xs (W.aw i) = 0 := xsum_other W jb _ (fun i' ↦ (W.xa i' i).symm)
      by_cases hi : i = 0
      · subst hi; simp [hc, hx, aval]
      · have hne : W.aw i ≠ W.aw 0 := fun h ↦ hi (W.aw_inj h)
        have hv : ¬ i.val ≤ 0 := fun h ↦ hi (Fin.ext (by simpa using h))
        simp [hc, hx, Pi.single_apply, hne, hv]
    · have hx : xs (W.xw i) = if jb i = 0 then 1 else 0 := xsum_xw W jb i
      have hne : W.xw i ≠ W.aw 0 := W.xa i 0
      rw [Pi.add_apply, Pi.add_apply, hx, Pi.single_apply, if_neg hne]
      rcases bit_cases (jb i) with h | h <;> simp [h, one_add_one_zmod2]
    · have hx : xs w = 0 := xsum_other W jb w hw2
      rw [Pi.add_apply, Pi.add_apply, hx, Pi.single_apply, if_neg (hw1 0)]
      simp
  obtain ⟨γ, hγ, hket⟩ := chain_ket W jb β _ hinv0 b le_rfl
  refine ⟨γ, hγ, ?_⟩
  have h1 : (Circuit.X (W.aw 0)).eval.1.mulVec (ket β) = ket (β + Pi.single (W.aw 0) 1) := by
    rw [ket_X, update_eq_add_single]
  have h2 := xl_ket W jb (List.finRange b) (β + Pi.single (W.aw 0) 1)
  rw [← Fin.sum_univ_def] at h2
  simp only [wcirc, eval_seq_mulVec, h1]
  rw [xlayer, h2, hket]

end Wires


namespace Wires

variable {b N n : ℕ} (W : Wires b N n)

/-- The classical flag: `1` iff the index bits equal `jb`. -/
theorem aval_zero_or_one (jb : Fin b → ZMod 2) (β : BitAssignment n) :
    ∀ k, W.aval jb β k = 0 ∨ W.aval jb β k = 1 := fun k ↦ bit_cases _

theorem aval_eq_one_iff (jb : Fin b → ZMod 2) (β : BitAssignment n) :
    ∀ k, k ≤ b → (W.aval jb β k = 1 ↔ ∀ i : Fin b, i.val < k → β (W.xw i) = jb i) := by
  intro k
  induction k with
  | zero => intro _; simp [aval]
  | succ k ih =>
    intro hk
    have hk' : k < b := by omega
    have ih' := ih (by omega)
    have hx : W.xp jb β k = 1 ↔ β (W.xw ⟨k, hk'⟩) = jb ⟨k, hk'⟩ := by
      simp only [xp, hk', dite_true]
      rcases bit_cases (β (W.xw ⟨k, hk'⟩)) with h | h <;>
        rcases bit_cases (jb ⟨k, hk'⟩) with h' | h' <;> simp [h, h', one_add_one_zmod2]
    have hmul : ∀ x y : ZMod 2, x * y = 1 ↔ x = 1 ∧ y = 1 := by decide
    rw [aval, hmul, ih', hx]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      by_cases hik : i.val < k
      · exact h1 i hik
      · have : i = ⟨k, hk'⟩ := Fin.ext (show i.val = k by omega)
        subst this; exact h2
    · intro h
      exact ⟨fun i hi ↦ h i (by omega), h ⟨k, hk'⟩ (show k < k + 1 by omega)⟩

/-- The sign gate: `Z` on the flag wire when the term is negative. -/
def signGate (s : Bool) : Circuit n :=
  if s then Circuit.Z (W.aw (Fin.last b)) else Circuit.identity

theorem hsw_flag (q : Fin N) : W.aw (Fin.last b) ≠ W.sw q := (W.sa q _).symm

/-- One term: compute the flag, apply the controlled signed string, uncompute. -/
def term (jb : Fin b → ZMod 2) (s : Bool) (row : Fin N → Pauli) : Circuit n :=
  .seq (W.wcirc jb)
    (.seq (.seq (ctrlStr (W.aw (Fin.last b)) W.sw W.hsw_flag row) (W.signGate s))
      (W.wcirc jb).inverse)

/-- Vector of the system flips. -/
noncomputable def sysAdd (row : Fin N → Pauli) : BitAssignment n :=
  ∑ q : Fin N, Pi.single (W.sw q) (pf (row q))

theorem sysAdd_sx (row : Fin N → Pauli) (i : Fin b) : W.sysAdd row (W.xw i) = 0 := by
  simp only [sysAdd, Finset.sum_apply, Pi.single_apply]
  exact Finset.sum_eq_zero fun q _ ↦ by simp [(W.sx q i).symm]

theorem sysAdd_sa (row : Fin N → Pauli) (k : Fin (b + 1)) : W.sysAdd row (W.aw k) = 0 := by
  simp only [sysAdd, Finset.sum_apply, Pi.single_apply]
  exact Finset.sum_eq_zero fun q _ ↦ by simp [(W.sa q k).symm]

theorem sysAdd_other (row : Fin N → Pauli) (w : Wire n) (h : ∀ q, w ≠ W.sw q) :
    W.sysAdd row w = 0 := by
  simp only [sysAdd, Finset.sum_apply, Pi.single_apply]
  exact Finset.sum_eq_zero fun q _ ↦ by simp [h q]

theorem sysAdd_sw (row : Fin N → Pauli) (q : Fin N) : W.sysAdd row (W.sw q) = pf (row q) := by
  simp only [sysAdd, Finset.sum_apply, Pi.single_apply]
  rw [Finset.sum_eq_single q]
  · simp
  · intro q' _ hne; simp [W.sw_inj.eq_iff, Ne.symm hne]
  · simp

theorem sign_ket0 (s : Bool) (γ : BitAssignment n) (hf : γ (W.aw (Fin.last b)) = 0) :
    (W.signGate s).eval.1.mulVec (ket γ) = ket γ := by
  cases s
  · simp only [signGate, Bool.false_eq_true, if_false]; exact id_mulVec _
  · simp only [signGate, if_true, ket_Z, hf]; simp [bitSign]

theorem sign_ket1 (s : Bool) (γ : BitAssignment n) (hf : γ (W.aw (Fin.last b)) = 1) :
    (W.signGate s).eval.1.mulVec (ket γ) = (if s then (-1 : ℂ) else 1) • ket γ := by
  cases s
  · simp only [signGate, Bool.false_eq_true, if_false, one_smul]; exact id_mulVec _
  · simp only [signGate, if_true, ket_Z, hf]; simp [bitSign]

theorem term_ket_zero (jb : Fin b → ZMod 2) (s : Bool) (row : Fin N → Pauli)
    (β : BitAssignment n) (hc : ∀ k, β (W.aw k) = 0) (hf : W.aval jb β b = 0) :
    (W.term jb s row).eval.1.mulVec (ket β) = ket β := by
  obtain ⟨γ, hγ, hket⟩ := W.wcirc_ket jb β hc
  have hflag : γ (W.aw (Fin.last b)) = 0 := by
    have := hγ.1 (Fin.last b); simpa [hf] using this
  simp only [term, eval_seq_mulVec, hket]
  rw [ctrlStr, ctrlList_ket0 _ _ _ _ _ _ hflag, W.sign_ket0 s γ hflag, ← hket]
  exact inv_mulVec _ _

theorem term_ket_one (jb : Fin b → ZMod 2) (s : Bool) (row : Fin N → Pauli)
    (β : BitAssignment n) (hc : ∀ k, β (W.aw k) = 0) (hf : W.aval jb β b = 1) :
    (W.term jb s row).eval.1.mulVec (ket β) =
      ((List.map (fun q ↦ pc (row q) (β (W.sw q))) (List.finRange N)).prod *
        (if s then (-1 : ℂ) else 1)) • ket (β + W.sysAdd row) := by
  obtain ⟨γ, hγ, hket⟩ := W.wcirc_ket jb β hc
  have hflag : γ (W.aw (Fin.last b)) = 1 := by
    have := hγ.1 (Fin.last b); simpa [hf] using this
  have hclean : ∀ k, (β + W.sysAdd row) (W.aw k) = 0 := fun k ↦ by
    simp [hc, W.sysAdd_sa]
  obtain ⟨γ', hγ', hket'⟩ := W.wcirc_ket jb (β + W.sysAdd row) hclean
  have hshift := W.Inv_shift hγ (W.sysAdd row) (W.sysAdd_sx row) (W.sysAdd_sa row)
  have heq : γ' = γ + W.sysAdd row := W.Inv_ext hγ' hshift
  have hsum : ∑ q ∈ (List.finRange N).toFinset, (Pi.single (W.sw q) (pf (row q)) : BitAssignment n)
      = W.sysAdd row := by
    rw [sysAdd]; congr 1; ext q; simp
  have hph : (List.map (fun q ↦ pc (row q) (γ (W.sw q))) (List.finRange N)) =
      List.map (fun q ↦ pc (row q) (β (W.sw q))) (List.finRange N) := by
    refine List.map_congr_left fun q _ ↦ ?_
    rw [hγ.2.2 (W.sw q) (fun i ↦ W.sa q i) (fun i ↦ W.sx q i)]
  have hflag' : (γ + W.sysAdd row) (W.aw (Fin.last b)) = 1 := by
    simp [hflag, W.sysAdd_sa]
  simp only [term, eval_seq_mulVec, hket]
  rw [ctrlStr, ctrlList_ket1 _ _ _ W.sw_inj _ _ (List.nodup_finRange N) _ hflag, hsum, hph,
    Matrix.mulVec_smul]
  rw [W.sign_ket1 s _ hflag', Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul]
  rw [← heq, ← hket', inv_mulVec]

end Wires

/-- Index bits of `j`, least significant first, as elements of `ZMod 2`. -/
def bitsZ (b j : ℕ) : Fin b → ZMod 2 := fun i ↦ ((j / 2 ^ i.val % 2 : ℕ) : ZMod 2)

theorem bitsZ_inj {b j j' : ℕ} (hj : j < 2 ^ b) (hj' : j' < 2 ^ b)
    (h : bitsZ b j = bitsZ b j') : j = j' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < b
  · have h1 := congrFun h ⟨i, hi⟩
    simp only [bitsZ] at h1
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_mod, Nat.mod_mod] at h1
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, h1]
  · have hb : 2 ^ b ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hj hb),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hj' hb)]

namespace Wires

variable {b N n : ℕ} (W : Wires b N n)

/-- Terms for the table, in order of `j`. -/
def termList {L : ℕ} (tbl : Fin L → Bool × (Fin N → Pauli)) : List (Circuit n) :=
  (List.finRange L).map fun j ↦ W.term (bitsZ b j.val) (tbl j).1 (tbl j).2

/-- Flag of term `j` is `0` when the index bits differ from those of `j`. -/
theorem flag_zero_of_ne (j j' : ℕ) (hj : j < 2 ^ b) (hj' : j' < 2 ^ b) (hne : j ≠ j')
    (β : BitAssignment n) (hβ : ∀ i : Fin b, β (W.xw i) = bitsZ b j' i) :
    W.aval (bitsZ b j) β b = 0 := by
  rcases W.aval_zero_or_one (bitsZ b j) β b with h | h
  · exact h
  · exfalso
    have := (W.aval_eq_one_iff (bitsZ b j) β b le_rfl).1 h
    apply hne
    apply bitsZ_inj hj hj'
    funext i
    rw [← hβ i]; exact (this i i.2).symm

theorem flag_one_of_eq (j : ℕ) (β : BitAssignment n) (hβ : ∀ i : Fin b, β (W.xw i) = bitsZ b j i) :
    W.aval (bitsZ b j) β b = 1 :=
  (W.aval_eq_one_iff (bitsZ b j) β b le_rfl).2 fun i _ ↦ hβ i

theorem termList_none {L : ℕ} (hLb : L ≤ 2 ^ b) (tbl : Fin L → Bool × (Fin N → Pauli))
    (l : List (Fin L)) (j' : ℕ) (hj' : j' < 2 ^ b) (hnot : ∀ j ∈ l, j.val ≠ j')
    (β : BitAssignment n) (hc : ∀ k, β (W.aw k) = 0)
    (hβ : ∀ i : Fin b, β (W.xw i) = bitsZ b j' i) :
    (Circuit.sequence (l.map fun j ↦ W.term (bitsZ b j.val) (tbl j).1 (tbl j).2)).eval.1.mulVec
        (ket β) = ket β := by
  induction l with
  | nil =>
    rw [List.map_nil, Circuit.sequence_nil, Circuit.eval_identity]
    exact Matrix.one_mulVec _
  | cons j l ih =>
    rw [List.map_cons, Circuit.sequence_cons, eval_seq_mulVec,
      W.term_ket_zero _ _ _ β hc
        (W.flag_zero_of_ne j.val j' (lt_of_lt_of_le j.2 hLb) hj'
          (hnot j (List.mem_cons_self ..)) β hβ)]
    exact ih (fun j hj ↦ hnot j (List.mem_cons_of_mem _ hj))

theorem termList_some {L : ℕ} (hLb : L ≤ 2 ^ b) (tbl : Fin L → Bool × (Fin N → Pauli))
    (l : List (Fin L)) (hl : l.Nodup) (j0 : Fin L) (hj0 : j0 ∈ l)
    (β : BitAssignment n) (hc : ∀ k, β (W.aw k) = 0)
    (hβ : ∀ i : Fin b, β (W.xw i) = bitsZ b j0.val i) :
    (Circuit.sequence (l.map fun j ↦ W.term (bitsZ b j.val) (tbl j).1 (tbl j).2)).eval.1.mulVec
        (ket β) =
      ((List.map (fun q ↦ pc ((tbl j0).2 q) (β (W.sw q))) (List.finRange N)).prod *
        (if (tbl j0).1 then (-1 : ℂ) else 1)) • ket (β + W.sysAdd (tbl j0).2) := by
  induction l with
  | nil => exact absurd hj0 (by simp)
  | cons j l ih =>
    rw [List.map_cons, Circuit.sequence_cons, eval_seq_mulVec]
    by_cases hj : j = j0
    · subst hj
      rw [W.term_ket_one _ _ _ β hc (W.flag_one_of_eq _ β hβ), Matrix.mulVec_smul]
      have hβ' : ∀ i : Fin b, (β + W.sysAdd (tbl j).2) (W.xw i) = bitsZ b j.val i := fun i ↦ by
        simp [hβ, W.sysAdd_sx]
      have hc' : ∀ k, (β + W.sysAdd (tbl j).2) (W.aw k) = 0 := fun k ↦ by
        simp [hc, W.sysAdd_sa]
      rw [termList_none W hLb tbl l j.val (lt_of_lt_of_le j.2 hLb) (fun j' hj' ↦ ?_) _ hc' hβ']
      intro h
      exact (List.nodup_cons.1 hl).1 (by
        have : j' = j := Fin.ext h
        exact this ▸ hj')
    · have hmem : j0 ∈ l := by
        rcases List.mem_cons.1 hj0 with h | h
        · exact absurd h.symm hj
        · exact h
      rw [W.term_ket_zero _ _ _ β hc
        (W.flag_zero_of_ne j.val j0.val (lt_of_lt_of_le j.2 hLb) (lt_of_lt_of_le j0.2 hLb)
          (fun h ↦ hj (Fin.ext h)) β hβ)]
      exact ih (List.nodup_cons.1 hl).2 hmem

end Wires

namespace Wires

variable {b N n : ℕ} (W : Wires b N n)

theorem count_ctrlPauli {n : ℕ} (c t : Wire n) (h : c ≠ t) (p : Pauli) :
    (ctrlPauli c t h p).count PrimitiveGate.T = 0 ∧
      (ctrlPauli c t h p).count PrimitiveGate.TOFF = 0 := by
  cases p <;> simp [ctrlPauli, count_T_fixupCZ, count_TOFF_fixupCZ] <;> exact ⟨rfl, rfl⟩

theorem count_ctrlStr {N n : ℕ} (c : Wire n) (sw : Fin N → Wire n) (hsw : ∀ q, c ≠ sw q)
    (row : Fin N → Pauli) :
    (ctrlStr c sw hsw row).count PrimitiveGate.T = 0 ∧
      (ctrlStr c sw hsw row).count PrimitiveGate.TOFF = 0 := by
  unfold ctrlStr
  rw [Circuit.count_sequence, Circuit.count_sequence]
  constructor
  · apply List.sum_eq_zero
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨q, _, rfl⟩ := List.mem_map.1 hy
    exact (count_ctrlPauli _ _ _ _).1
  · apply List.sum_eq_zero
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨q, _, rfl⟩ := List.mem_map.1 hy
    exact (count_ctrlPauli _ _ _ _).2

theorem count_xlayer (jb : Fin b → ZMod 2) :
    (W.xlayer jb).count PrimitiveGate.T = 0 ∧ (W.xlayer jb).count PrimitiveGate.TOFF = 0 := by
  unfold xlayer
  rw [Circuit.count_sequence, Circuit.count_sequence]
  constructor <;>
  · apply List.sum_eq_zero
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨q, _, rfl⟩ := List.mem_map.1 hy
    split_ifs <;> first | rfl | simp

theorem count_chainN (k : ℕ) :
    (W.chainN k).count PrimitiveGate.T ≤ 4 * k ∧ (W.chainN k).count PrimitiveGate.TOFF = 0 := by
  induction k with
  | zero => exact ⟨le_rfl, rfl⟩
  | succ k ih =>
    unfold chainN
    rw [Circuit.count_seq, Circuit.count_seq]
    by_cases hk : k < b
    · simp only [hk, dite_true, andStep, count_T_AND4T, count_TOFF_AND4T]
      exact ⟨by omega, by omega⟩
    · simp only [hk, dite_false]
      exact ⟨by have := ih.1; simp; omega, by simp [ih.2]⟩

theorem count_wcirc (jb : Fin b → ZMod 2) :
    (W.wcirc jb).count PrimitiveGate.T ≤ 4 * b ∧ (W.wcirc jb).count PrimitiveGate.TOFF = 0 := by
  have hx := W.count_xlayer jb
  have hc := W.count_chainN b
  unfold wcirc
  rw [Circuit.count_seq, Circuit.count_seq, Circuit.count_seq, Circuit.count_seq]
  have h1 : (Circuit.X (W.aw 0)).count PrimitiveGate.T = 0 := rfl
  have h2 : (Circuit.X (W.aw 0)).count PrimitiveGate.TOFF = 0 := rfl
  exact ⟨by omega, by omega⟩

theorem count_signGate (s : Bool) :
    (W.signGate s).count PrimitiveGate.T = 0 ∧ (W.signGate s).count PrimitiveGate.TOFF = 0 := by
  cases s <;> exact ⟨rfl, rfl⟩

theorem count_term (jb : Fin b → ZMod 2) (s : Bool) (row : Fin N → Pauli) :
    (W.term jb s row).count PrimitiveGate.T ≤ 8 * b ∧
      (W.term jb s row).count PrimitiveGate.TOFF = 0 := by
  have h := W.count_wcirc jb
  have hs := W.count_signGate s
  have hcs := count_ctrlStr (W.aw (Fin.last b)) W.sw W.hsw_flag row
  have i1 : (W.wcirc jb).inverse.count PrimitiveGate.T = (W.wcirc jb).count PrimitiveGate.T :=
    Circuit.count_inverse_of_ne _ (by simp) (by simp) _
  have i2 : (W.wcirc jb).inverse.count PrimitiveGate.TOFF = (W.wcirc jb).count PrimitiveGate.TOFF :=
    Circuit.count_inverse_of_ne _ (by simp) (by simp) _
  unfold term
  simp only [Circuit.count_seq]
  exact ⟨by omega, by omega⟩

/-- The full circuit: one term per table row. -/
def full {L : ℕ} (tbl : Fin L → Bool × (Fin N → Pauli)) : Circuit n :=
  Circuit.sequence ((List.finRange L).map fun j ↦ W.term (bitsZ b j.val) (tbl j).1 (tbl j).2)

theorem count_full {L : ℕ} (tbl : Fin L → Bool × (Fin N → Pauli)) :
    (W.full tbl).count PrimitiveGate.T ≤ 8 * b * L ∧
      (W.full tbl).count PrimitiveGate.TOFF = 0 := by
  unfold full
  rw [Circuit.count_sequence, Circuit.count_sequence, List.map_map, List.map_map]
  constructor
  · have : ∀ x ∈ (List.finRange L).map ((Circuit.count PrimitiveGate.T) ∘ fun j : Fin L ↦
        W.term (bitsZ b j.val) (tbl j).1 (tbl j).2), x ≤ 8 * b := by
      intro x hx
      obtain ⟨j, _, rfl⟩ := List.mem_map.1 hx
      exact (W.count_term _ _ _).1
    have h := List.sum_le_length_nsmul _ _ this
    simpa [mul_comm] using h
  · apply List.sum_eq_zero
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hx
    exact (W.count_term _ _ _).2

end Wires

/-- Wires of a disjoint placement. -/
def mkWires {b N n : ℕ} (rData : QRegister (N + b) n) (rAnc : QRegister (b + 1) n)
    (hd : ∀ i j, rData i ≠ rAnc j) : Wires b N n where
  sw q := rData ⟨q.val, by omega⟩
  xw i := rData ⟨N + i.val, by omega⟩
  aw k := rAnc k
  sw_inj := fun a c h ↦ by
    have := rData.wires.injective h
    exact Fin.ext (by simpa using congrArg Fin.val this)
  xw_inj := fun a c h ↦ by
    have := rData.wires.injective h
    exact Fin.ext (by simpa using congrArg Fin.val this)
  aw_inj := rAnc.wires.injective
  sx := fun q i h ↦ by
    have := rData.wires.injective h
    have := congrArg Fin.val this
    simp at this; omega
  sa := fun q k ↦ hd _ _
  xa := fun i k ↦ hd _ _

theorem qreg_ext {k n : ℕ} (r s : QRegister k n) (h : ∀ i, r i = s i) : r = s := by
  cases r with | mk r =>
  cases s with | mk s =>
  congr
  exact DFunLike.ext _ _ h

theorem concat_block_embed {k m n : ℕ} (rT : QRegister k n) (rA : QRegister m n)
    (hd : rT.DisjointWires rA) (U0 : Unitary (2 ^ k)) :
    ((rT.concat rA hd).embedUnitary ((QRegister.block 0 k (by omega) : QRegister k (k + m)).embedUnitary U0)).1
      = rT.embedMatrix U0.1 := by
  rw [← QRegister.embedUnitary_compose, QRegister.embedUnitary_val]
  have : (rT.concat rA hd).compose (QRegister.block 0 k (by omega)) = rT := by
    apply qreg_ext
    intro i
    rw [QRegister.compose_apply]
    have : QRegister.block 0 k (by omega) i = Fin.castAdd m i := Fin.ext (by simp [QRegister.block_apply_val])
    rw [this, QRegister.concat_apply_left]
  rw [this]

theorem flips_apply {N : ℕ} (row : Fin N → Pauli) (q : Fin N) :
    (∑ q' ∈ (List.finRange N).toFinset, (Pi.single q' (pf (row q')) : BitAssignment N)) q = pf (row q) := by
  simp only [Finset.sum_apply, Pi.single_apply]
  rw [Finset.sum_eq_single q]
  · simp
  · intro q' _ hne; simp [Ne.symm hne]
  · simp

theorem nat_bit_low (N a t y j : ℕ) (hN : N = a + (t + 1)) :
    (y + 2 ^ N * j) / 2 ^ a % 2 = y / 2 ^ a % 2 := by
  have h2 : 2 ^ N * j = 2 ^ a * (2 * (2 ^ t * j)) := by
    rw [hN, pow_add, pow_add]; ring
  rw [h2, Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ a)]
  omega

theorem nat_bit_high (N t y j : ℕ) (hy : y < 2 ^ N) :
    (y + 2 ^ N * j) / 2 ^ (N + t) % 2 = j / 2 ^ t % 2 := by
  rw [pow_add, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ N),
    Nat.div_eq_of_lt hy, zero_add]

theorem basisBits_dataEquiv (b N : ℕ) (j : Fin (2 ^ b)) (y : Fin (2 ^ N)) (i : Fin (N + b)) :
    basisBits (N + b) (selectPauliDataEquiv b N (j, y)) i =
      if h : i.val < N then basisBits N y ⟨i.val, h⟩ else basisBits b j ⟨i.val - N, by omega⟩ := by
  rw [basisBits_eq_div_mod]
  split_ifs with h
  · rw [basisBits_eq_div_mod]
    simp only [selectPauliDataEquiv_val]
    congr 1
    exact nat_bit_low N i.val (N - i.val - 1) y.val j.val (by omega)
  · rw [basisBits_eq_div_mod]
    simp only [selectPauliDataEquiv_val]
    congr 1
    obtain ⟨t, ht⟩ : ∃ t, i.val = N + t := ⟨i.val - N, by omega⟩
    have : i.val - N = t := by omega
    rw [this, ht]
    exact nat_bit_high N t y.val j.val y.2

theorem string_ket {N : ℕ} (row : Fin N → Pauli) (γ : BitAssignment N) :
    (selectPauliString row).1.mulVec (ket γ) =
      (List.map (fun q ↦ pc (row q) (γ q)) (List.finRange N)).prod •
        ket (γ + ∑ q ∈ (List.finRange N).toFinset, Pi.single q (pf (row q))) := by
  have := unitary_list_prod_ket row (List.finRange N) (List.nodup_finRange N) γ
  rw [selectPauliString, List.ofFn_eq_map]
  exact this

theorem term_ket {N : ℕ} (t : Bool × (Fin N → Pauli)) (γ : BitAssignment N) :
    (selectPauliTerm t).1.mulVec (ket γ) =
      ((if t.1 then (-1 : ℂ) else 1) * (List.map (fun q ↦ pc (t.2 q) (γ q)) (List.finRange N)).prod) •
        ket (γ + ∑ q ∈ (List.finRange N).toFinset, Pi.single q (pf (t.2 q))) := by
  have h : (selectPauliTerm t).1 = (selectPauliSign N t.1).1 * (selectPauliString t.2).1 := rfl
  rw [h, ← Matrix.mulVec_mulVec, string_ket, Matrix.mulVec_smul]
  rcases t with ⟨s, row⟩
  cases s
  · have hs : (selectPauliSign N false).1 = 1 := rfl
    rw [hs, Matrix.one_mulVec]
    simp only [Bool.false_eq_true, if_false, one_mul]
  · have hs : (selectPauliSign N true).1 = -1 := rfl
    rw [hs, Matrix.neg_mulVec, Matrix.one_mulVec]
    simp only [if_true, neg_mul, one_mul, neg_smul, smul_neg]

theorem mulVec_basisState {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (x y : Fin d) :
    (M.mulVec (basisState x)) y = M y x := by
  simp [Matrix.mulVec, dotProduct, basisState, Pi.single_apply]

theorem basisState_apply {d : ℕ} (z l : Fin d) :
    basisState z l = if l = z then 1 else 0 := by
  simp [basisState, Pi.single_apply]

/-- The completion of the table to all `2^b` index values used by `selectPauli_correctness`:
`tbl` on `j < L`, and the row `+I` on `j ≥ L`. -/
noncomputable def tblExt (b N L : ℕ) (tbl : SelectPauliTable L N) : SelectPauliTable (2 ^ b) N :=
  fun j ↦ if h : j.val < L then tbl ⟨j.val, h⟩ else (false, fun _ ↦ Pauli.I)

theorem tblExt_completes (b N L : ℕ) (tbl : SelectPauliTable L N) :
    SelectPauliCompletes b N L tbl (tblExt b N L tbl) := by
  intro j h
  simp only [tblExt, dif_pos j.2]

theorem hkey_main {b N L n : ℕ} (hLb : L ≤ 2 ^ b) (tbl : SelectPauliTable L N)
    (rT : QRegister (N + b) n) (rA : QRegister (b + 1) n) (hd : rT.DisjointWires rA)
    (β : BitAssignment n) (h0 : localIdx rA β = 0) :
    ((mkWires rT rA hd.ne).full tbl).eval.1.mulVec (ket β) =
      (rT.embedUnitary (selectPauliUnitary b N (2 ^ b) (tblExt b N L tbl))).1.mulVec
        (ket β) := by
  set W := mkWires rT rA hd.ne with hW
  have hc : ∀ k, β (W.aw k) = 0 := fun k ↦ SelectPauliBridge.bits_zero_of_localIdx_eq_zero rA β h0 k
  set idx := localIdx rT β with hidx
  obtain ⟨⟨j, x⟩, hjx⟩ := (selectPauliDataEquiv b N).surjective idx
  have hbits : ∀ i : Fin (N + b), β (rT i) = basisBits (N + b) idx i := fun i ↦ by
    simp [hidx, localIdx]
  have hbx : ∀ q : Fin N, β (W.sw q) = basisBits N x q := fun q ↦ by
    have := hbits ⟨q.val, by omega⟩
    rw [← hjx, basisBits_dataEquiv, dif_pos q.2] at this
    exact this
  have hbj : ∀ i : Fin b, β (W.xw i) = basisBits b j i := fun i ↦ by
    have := hbits ⟨N + i.val, by omega⟩
    rw [← hjx, basisBits_dataEquiv, dif_neg (by simp)] at this
    exact this.trans (congrArg (basisBits b j) (Fin.ext (by simp)))
  have hβ : ∀ i : Fin b, β (W.xw i) = bitsZ b j.val i := fun i ↦ by
    rw [hbj, basisBits_eq_div_mod]; rfl
  set t := tblExt b N L tbl j with ht
  have hL : ((W.full tbl).eval.1).mulVec (ket β) =
      ((List.map (fun q ↦ pc (t.2 q) (β (W.sw q))) (List.finRange N)).prod *
        (if t.1 then (-1 : ℂ) else 1)) • ket (β + W.sysAdd t.2) := by
    by_cases hjL : j.val < L
    · have ht' : t = tbl ⟨j.val, hjL⟩ := by simp only [ht, tblExt, dif_pos hjL]
      rw [ht']
      exact W.termList_some hLb tbl (List.finRange L) (List.nodup_finRange L) ⟨j.val, hjL⟩
        (List.mem_finRange _) β hc hβ
    · have ht' : t = (false, fun _ ↦ Pauli.I) := by simp only [ht, tblExt, dif_neg hjL]
      have hn := W.termList_none hLb tbl (List.finRange L) j.val j.2
        (fun j' _ ↦ fun h ↦ hjL (h ▸ j'.2)) β hc hβ
      have hsys : W.sysAdd (fun _ : Fin N ↦ Pauli.I) = 0 := by
        simp [Wires.sysAdd, pf]
      have hfull : ((W.full tbl).eval.1).mulVec (ket β) = ket β := hn
      rw [hfull, ht']
      simp [pc, hsys]
  rw [hL]
  have hU : (rT.embedUnitary (selectPauliUnitary b N (2 ^ b) (tblExt b N L tbl))).1 =
      rT.embedMatrix (selectPauliUnitary b N (2 ^ b) (tblExt b N L tbl)).1 := by
    rw [QRegister.embedUnitary_val]
  rw [hU, embedMatrix_mulVec_ket]
  have hterm := term_ket t (basisBits N x)
  have hket : ket (basisBits N x) = basisState x := by
    show basisState ((basisBits N).symm (basisBits N x)) = _
    rw [Equiv.symm_apply_apply]
  rw [hket] at hterm
  set y0 : Fin (2 ^ N) := (basisBits N).symm (basisBits N x +
    ∑ q ∈ (List.finRange N).toFinset, Pi.single q (pf (t.2 q))) with hy0
  set c0 : ℂ := ((if t.1 then (-1 : ℂ) else 1) *
    (List.map (fun q ↦ pc (t.2 q) (basisBits N x q)) (List.finRange N)).prod) with hc0
  have hcol : ∀ y, (selectPauliTerm t).1 y x = c0 * basisState y0 y := fun y ↦ by
    refine (mulVec_basisState (selectPauliTerm t).1 x y).symm.trans ?_
    rw [hterm]
    rfl
  have hcolU : (selectPauliUnitary b N (2 ^ b) (tblExt b N L tbl)).1 *ᵥ
      basisState (selectPauliDataEquiv b N (j, x)) =
      ∑ y : Fin (2 ^ N), (selectPauliTerm t).1 y x • basisState (selectPauliDataEquiv b N (j, y)) :=
    selectPauliUnitary_mulVec_basisState b N (2 ^ b) (tblExt b N L tbl) j j.2 x
  have hU0 : ∀ l, (selectPauliUnitary b N (2 ^ b) (tblExt b N L tbl)).1 l idx =
      c0 * basisState (selectPauliDataEquiv b N (j, y0)) l := fun l ↦ by
    refine (mulVec_basisState (selectPauliUnitary b N (2 ^ b) (tblExt b N L tbl)).1 idx l).symm.trans ?_
    rw [← hjx, congrFun hcolU l]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hcol, basisState_apply]
    rw [Finset.sum_eq_single y0]
    · simp [basisState_apply]
    · intro y _ hy
      simp [basisState_apply, hy]
    · simp
  have hK : writeReg β rT (basisBits (N + b) (selectPauliDataEquiv b N (j, y0))) =
      β + W.sysAdd t.2 := by
    funext w
    by_cases hw : w ∈ Set.range rT.wires
    · obtain ⟨i, rfl⟩ := hw
      rw [writeReg_apply_reg, basisBits_dataEquiv]
      by_cases hi : i.val < N
      · rw [dif_pos hi]
        have hy : basisBits N y0 ⟨i.val, hi⟩ = (basisBits N x +
            ∑ q ∈ (List.finRange N).toFinset, Pi.single q (pf (t.2 q))) ⟨i.val, hi⟩ := by
          simp [hy0]
        rw [hy, Pi.add_apply, flips_apply]
        have hs : rT.wires i = W.sw ⟨i.val, hi⟩ := rfl
        rw [hs, Pi.add_apply, W.sysAdd_sw, hbx]
      · rw [dif_neg hi]
        have hs : rT.wires i = W.xw ⟨i.val - N, by omega⟩ := by
          show rT.wires i = rT.wires ⟨N + (i.val - N), _⟩
          congr 1; ext; simp; omega
        rw [hs, Pi.add_apply, W.sysAdd_sx, add_zero, hbj]
    · rw [writeReg_apply_of_not_mem _ _ _ _ hw, Pi.add_apply,
        W.sysAdd_other _ _ (fun q h ↦ hw ⟨_, h.symm⟩), add_zero]
  have hsum : ∑ l, (selectPauliUnitary b N (2 ^ b) (tblExt b N L tbl)).1 l idx •
      ket (writeReg β rT (basisBits (N + b) l)) =
      c0 • ket (writeReg β rT (basisBits (N + b) (selectPauliDataEquiv b N (j, y0)))) := by
    simp only [hU0]
    rw [Finset.sum_eq_single (selectPauliDataEquiv b N (j, y0))]
    · simp [basisState_apply]
    · intro l _ hl; simp [basisState_apply, hl]
    · simp
  rw [hsum, hK]
  have hmap : List.map (fun q ↦ pc (t.2 q) (basisBits N x q)) (List.finRange N) =
      List.map (fun q ↦ pc (t.2 q) (β (W.sw q))) (List.finRange N) :=
    List.map_congr_left fun q _ ↦ by rw [hbx q]
  rw [hc0, hmap, mul_comm]

end SelectPauliImpl

end QuantumComputation.Specs

namespace QuantumComputation.Specs

open Operator Matrix

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive Prepare.Var where | v deriving DecidableEq, Inhabited

open Prepare (Var)
open Prepare.Var (v)

namespace PrepareImpl

open SelectPauliSteps SelectPauliImpl Finset Operator Matrix
open SelectPauli (Pauli)

open Finset

/-- Integer counts `c_j` summing to `M` with `|c_j - M w_j / λ| ≤ 1` (floors of partial sums). -/
theorem exists_counts (M L : ℕ) (w : PrepareWeights L) (hw : ∀ j, 0 ≤ w j)
    (hsum : 0 < prepareLambda w) :
    ∃ c : Fin L → ℕ, (∑ j, c j = M) ∧
      ∀ j, |(c j : ℚ) - M * w j / prepareLambda w| ≤ 1 := by
  set lam := prepareLambda w with hlam
  let S : ℕ → ℚ := fun j ↦ ∑ i : Fin L, if i.val < j then w i else 0
  have hSmono : Monotone S := fun a b hab ↦ by
    refine Finset.sum_le_sum fun i _ ↦ ?_
    by_cases h : i.val < a
    · simp [h, lt_of_lt_of_le h hab]
    · simp only [h, if_false]
      split_ifs <;> simp [hw i]
  have hS0 : S 0 = 0 := by simp [S]
  have hSL : S L = lam := by
    simp [S, hlam, prepareLambda]
  have hSsucc : ∀ j : Fin L, S (j.val + 1) = S j.val + w j := fun j ↦ by
    simp only [S]
    rw [show w j = ∑ i : Fin L, if i = j then w i else 0 by simp, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases h1 : i.val < j.val
    · have hij : i ≠ j := fun h ↦ by subst h; exact lt_irrefl _ h1
      simp [h1, hij, Nat.lt_succ_of_lt h1]
    · by_cases h2 : i = j
      · subst h2; simp
      · have : ¬ i.val < j.val + 1 := by
          have := Fin.val_ne_of_ne h2
          omega
        simp [h1, this, h2]
  let C : ℕ → ℕ := fun j ↦ ⌊(M : ℚ) * S j / lam⌋₊
  have hCmono : Monotone C := fun a b hab ↦ by
    apply Nat.floor_mono
    have := hSmono hab
    have hM : (0 : ℚ) ≤ M := Nat.cast_nonneg M
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this hM) hsum.le
  have hC0 : C 0 = 0 := by simp [C, hS0]
  have hCL : C L = M := by
    simp only [C, hSL]
    rw [mul_div_assoc, div_self hsum.ne', mul_one]
    exact Nat.floor_natCast M
  refine ⟨fun j ↦ C (j.val + 1) - C j.val, ?_, ?_⟩
  · rw [Fin.sum_univ_eq_sum_range (fun j ↦ C (j + 1) - C j) L,
      Finset.sum_range_tsub hCmono, hCL, hC0, Nat.sub_zero]
  · intro j
    have hle : C j.val ≤ C (j.val + 1) := hCmono (Nat.le_succ _)
    have hA := Nat.floor_le (show (0 : ℚ) ≤ (M : ℚ) * S j.val / lam from
      div_nonneg (mul_nonneg (Nat.cast_nonneg M) (Finset.sum_nonneg fun i _ ↦ by
        split_ifs <;> simp [hw i])) hsum.le)
    have hB := Nat.floor_le (show (0 : ℚ) ≤ (M : ℚ) * S (j.val + 1) / lam from
      div_nonneg (mul_nonneg (Nat.cast_nonneg M) (Finset.sum_nonneg fun i _ ↦ by
        split_ifs <;> simp [hw i])) hsum.le)
    have hA' := Nat.lt_floor_add_one ((M : ℚ) * S j.val / lam)
    have hB' := Nat.lt_floor_add_one ((M : ℚ) * S (j.val + 1) / lam)
    have hsplit : (M : ℚ) * S (j.val + 1) / lam = (M : ℚ) * S j.val / lam + M * w j / lam := by
      rw [hSsucc j]; ring
    rw [Nat.cast_sub hle]
    change |((C (j.val + 1) : ℕ) : ℚ) - (C j.val : ℕ) - _| ≤ 1
    simp only [C] at hA hB hA' hB' ⊢
    rw [abs_le]
    constructor <;> nlinarith [hsplit]



open Finset

/-- A function with prescribed fibre sizes. -/
theorem exists_fun_of_counts {L M : ℕ} (c : Fin L → ℕ) (h : ∑ j, c j = M) :
    ∃ F : Fin M → Fin L, ∀ j, (univ.filter (fun σ ↦ F σ = j)).card = c j := by
  subst h
  refine ⟨fun σ ↦ (finSigmaFinEquiv.symm σ).1, fun j ↦ ?_⟩
  have h1 : (univ.filter (fun σ : Fin (∑ j, c j) ↦ (finSigmaFinEquiv.symm σ).1 = j)).card =
      (univ.filter (fun s : (Σ i, Fin (c i)) ↦ s.1 = j)).card := by
    refine Finset.card_nbij' (fun σ ↦ finSigmaFinEquiv.symm σ) (fun s ↦ finSigmaFinEquiv s) ?_ ?_ ?_ ?_
    · intro σ hσ; simpa using hσ
    · intro s hs; simpa using hs
    · intro σ _; simp
    · intro s _; simp
  rw [h1]
  have h2 : (univ.filter (fun s : (Σ i, Fin (c i)) ↦ s.1 = j)) =
      (univ : Finset (Fin (c j))).map ⟨Sigma.mk j, sigma_mk_injective⟩ := by
    ext ⟨i, x⟩
    simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk, Sigma.mk.injEq]
    constructor
    · rintro rfl; exact ⟨x, rfl, HEq.rfl⟩
    · rintro ⟨y, rfl, h⟩; rfl
  rw [h2, card_map, card_univ, Fintype.card_fin]

/-- The classical fibre function: for `1 ≤ L ≤ 2^b`, valid weights, a function from `2^(b+μ)`
points to the index values `< L` with fibre sizes within `1` of `2^(b+μ) w_j / λ`. -/
theorem exists_fibres (b L μ : ℕ) (hLb : L ≤ 2 ^ b) (w : PrepareWeights L) (hw : ∀ j, 0 ≤ w j)
    (hsum : 0 < prepareLambda w) :
    ∃ F : Fin (2 ^ (b + μ)) → Fin (2 ^ b),
      (∀ σ, (F σ).val < L) ∧
      ∀ (j : Fin (2 ^ b)) (hj : j.val < L),
        |(((univ.filter (fun σ ↦ F σ = j)).card : ℝ) / 2 ^ (b + μ)) -
            ((w ⟨j.val, hj⟩ / prepareLambda w : ℚ) : ℝ)| ≤ 1 / (2 ^ μ * L) := by
  obtain ⟨c, hc, hcb⟩ := exists_counts (2 ^ (b + μ)) L w hw hsum
  obtain ⟨F0, hF0⟩ := exists_fun_of_counts c hc
  refine ⟨fun σ ↦ ⟨(F0 σ).val, lt_of_lt_of_le (F0 σ).2 hLb⟩, fun σ ↦ (F0 σ).2, ?_⟩
  intro j hj
  have hfib : (univ.filter (fun σ ↦ (⟨(F0 σ).val, lt_of_lt_of_le (F0 σ).2 hLb⟩ : Fin (2 ^ b)) = j)) =
      univ.filter (fun σ ↦ F0 σ = ⟨j.val, hj⟩) := by
    ext σ
    simp [Fin.ext_iff]
  rw [hfib, hF0]
  have hb := hcb ⟨j.val, hj⟩
  have hM : (0 : ℝ) < 2 ^ (b + μ) := by positivity
  have hb' : |((c ⟨j.val, hj⟩ : ℕ) : ℝ) - 2 ^ (b + μ) * ((w ⟨j.val, hj⟩ / prepareLambda w : ℚ) : ℝ)| ≤ 1 := by
    have := (Rat.cast_le (K := ℝ)).2 hb
    push_cast at this ⊢
    simpa [mul_div_assoc] using this
  have key : |((c ⟨j.val, hj⟩ : ℕ) : ℝ) / 2 ^ (b + μ) - ((w ⟨j.val, hj⟩ / prepareLambda w : ℚ) : ℝ)| ≤
      1 / 2 ^ (b + μ) := by
    have : ((c ⟨j.val, hj⟩ : ℕ) : ℝ) / 2 ^ (b + μ) - ((w ⟨j.val, hj⟩ / prepareLambda w : ℚ) : ℝ) =
        (((c ⟨j.val, hj⟩ : ℕ) : ℝ) - 2 ^ (b + μ) * ((w ⟨j.val, hj⟩ / prepareLambda w : ℚ) : ℝ)) /
          2 ^ (b + μ) := by
      field_simp
    rw [this, abs_div, abs_of_pos hM]
    exact div_le_div_of_nonneg_right hb' hM.le
  refine key.trans ?_
  have hL : (0 : ℝ) < L := by
    have : 0 < L := Nat.pos_of_ne_zero (by rintro rfl; exact absurd hj (by simp))
    exact_mod_cast this
  have hLb' : (L : ℝ) ≤ 2 ^ b := by exact_mod_cast hLb
  apply one_div_le_one_div_of_le (by positivity)
  rw [pow_add]
  nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) μ]



open Finset Operator Matrix

/-- Hadamards on the first `t` garbage wires `b, …, b + t - 1` of `b + g` wires. -/
def hPre (b g t : ℕ) (ht : t ≤ g) : Circuit (b + g) :=
  Circuit.sequence (List.ofFn fun i : Fin t ↦ Circuit.H (⟨b + i.val, by omega⟩ : Fin (b + g)))

/-- The bit assignment that is zero off the first `t` garbage wires and equals `γ` on them. -/
def extB (b g t : ℕ) (γ : Fin t → ZMod 2) : BitAssignment (b + g) := fun i ↦
  if h : b ≤ i.val ∧ i.val < b + t then γ ⟨i.val - b, by omega⟩ else 0

theorem hPre_succ (b g t : ℕ) (ht : t + 1 ≤ g) :
    (hPre b g (t + 1) ht).eval =
      (Circuit.H (⟨b + t, by omega⟩ : Fin (b + g))).eval * (hPre b g t (by omega)).eval := by
  unfold hPre
  rw [Circuit.eval_sequence, Circuit.eval_sequence, List.ofFn_succ', List.concat_eq_append,
    List.map_append, List.reverse_append]
  simp [Fin.val_last]

theorem extB_snoc (b g t : ℕ) (ht : t + 1 ≤ g) (γ : Fin t → ZMod 2) (a : ZMod 2) :
    extB b g (t + 1) (Fin.snoc γ a) =
      Function.update (extB b g t γ) (⟨b + t, by omega⟩ : Fin (b + g)) a := by
  funext i
  by_cases hi : i = (⟨b + t, by omega⟩ : Fin (b + g))
  · subst hi
    rw [Function.update_self]
    have key : ∀ h : b + t - b < t + 1, (Fin.snoc γ a : Fin (t + 1) → ZMod 2) ⟨b + t - b, h⟩ = a := by
      intro h
      have : (⟨b + t - b, h⟩ : Fin (t + 1)) = Fin.last t := Fin.ext (by simp)
      rw [this, Fin.snoc_last]
    unfold extB
    rw [dif_pos ⟨by simp, by simp⟩]
    exact key _
  · rw [Function.update_of_ne hi]
    have hi' : i.val ≠ b + t := fun h ↦ hi (Fin.ext h)
    unfold extB
    by_cases h1 : b ≤ i.val ∧ i.val < b + t
    · rw [dif_pos h1, dif_pos ⟨h1.1, by omega⟩]
      have : (⟨i.val - b, by omega⟩ : Fin (t + 1)) = Fin.castSucc ⟨i.val - b, by omega⟩ :=
        Fin.ext rfl
      rw [this, Fin.snoc_castSucc]
    · rw [dif_neg h1, dif_neg (by omega)]

theorem extB_wire_zero (b g t : ℕ) (ht : t + 1 ≤ g) (γ : Fin t → ZMod 2) :
    extB b g t γ (⟨b + t, by omega⟩ : Fin (b + g)) = 0 := by
  simp [extB]

theorem sum_zmod2 {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) : ∑ a, f a = f 0 + f 1 :=
  Fin.sum_univ_two f

theorem mulVec_mul_unitary {d : ℕ} (A B : Unitary d) (v : Fin d → ℂ) :
    (A * B).1.mulVec v = A.1.mulVec (B.1.mulVec v) := by
  rw [Matrix.mulVec_mulVec]; rfl

theorem hPre_ket (b g : ℕ) : ∀ (t : ℕ) (ht : t ≤ g),
    (hPre b g t ht).eval.1.mulVec (ket (0 : BitAssignment (b + g))) =
      ((Real.sqrt (1 / 2) : ℂ) ^ t) • ∑ γ : Fin t → ZMod 2, ket (extB b g t γ) := by
  intro t
  induction t with
  | zero =>
    intro ht
    have h0 : (hPre b g 0 ht).eval = 1 := by simp [hPre]
    have hz : ∀ γ : Fin 0 → ZMod 2, extB b g 0 γ = 0 := by
      intro γ; funext i; simp [extB]
    rw [h0]
    simp only [hz, Finset.univ_unique, Finset.sum_singleton, pow_zero, one_smul]
    exact Matrix.one_mulVec _
  | succ t ih =>
    intro ht
    rw [hPre_succ, mulVec_mul_unitary, ih (by omega), Matrix.mulVec_smul, Matrix.mulVec_sum]
    have hstep : ∀ γ : Fin t → ZMod 2,
        (Circuit.H (⟨b + t, by omega⟩ : Fin (b + g))).eval.1.mulVec (ket (extB b g t γ)) =
        (Real.sqrt (1 / 2) : ℂ) • ∑ a : ZMod 2, ket (extB b g (t + 1) (Fin.snoc γ a)) := by
      intro γ
      rw [ket_H, extB_wire_zero b g t ht γ]
      simp only [extB_snoc b g t ht, sum_zmod2]
      simp [bitSign]
    simp only [hstep]
    have hsplit : ∑ γ' : Fin (t + 1) → ZMod 2, ket (extB b g (t + 1) γ') =
        ∑ γ : Fin t → ZMod 2, ∑ a : ZMod 2, ket (extB b g (t + 1) (Fin.snoc γ a)) := by
      rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (t + 1) ↦ ZMod 2))
        (fun p ↦ ket (extB b g (t + 1) (Fin.snoc p.2 p.1)))
        (fun γ' ↦ ket (extB b g (t + 1) γ')) (fun p ↦ rfl)]
      exact Fintype.sum_prod_type_right _
    rw [hsplit, ← Finset.smul_sum, smul_smul, pow_succ]



open Finset Operator Matrix

/-- Pauli that flips exactly when the bit is set. -/
def pauliOfBit (a : ZMod 2) : Pauli := if a = 0 then Pauli.I else Pauli.X

/-- The `SELECT` table of a classical function `F`: term `σ` is `X^{bits of F σ}`. -/
def tblOf (b g : ℕ) (F : Fin (2 ^ g) → Fin (2 ^ b)) : SelectPauliTable (2 ^ g) b :=
  fun σ ↦ (false, fun q ↦ pauliOfBit (basisBits b (F σ) q))

theorem tbl_col (b g : ℕ) (F : Fin (2 ^ g) → Fin (2 ^ b)) (σ : Fin (2 ^ g)) :
    (selectPauliTerm (tblOf b g F σ)).1.mulVec (basisState 0) = basisState (F σ) := by
  have h0 : (basisState (0 : Fin (2 ^ b)) : Fin (2 ^ b) → ℂ) = ket 0 := by
    simp [ket]
  rw [h0, term_ket]
  have hp : ∀ q : Fin b, pc (pauliOfBit (basisBits b (F σ) q)) ((0 : BitAssignment b) q) = 1 := by
    intro q
    unfold pauliOfBit
    split_ifs <;> simp [pc]
  have hprod : (List.map (fun q ↦ pc ((tblOf b g F σ).2 q) ((0 : BitAssignment b) q))
      (List.finRange b)).prod = 1 := by
    simp only [tblOf, hp]
    simp
  have hflip : (0 : BitAssignment b) + ∑ q ∈ (List.finRange b).toFinset,
      Pi.single q (pf ((tblOf b g F σ).2 q)) = basisBits b (F σ) := by
    funext q
    rw [Pi.add_apply, flips_apply]
    simp only [tblOf, pauliOfBit, Pi.zero_apply, zero_add]
    split_ifs with h
    · simp [pf, h]
    · have := bit_cases (basisBits b (F σ) q)
      rcases this with h' | h'
      · exact absurd h' h
      · simp [pf, h']
  rw [hflip, hprod]
  simp [tblOf, ket]


theorem sel_col (b g : ℕ) (F : Fin (2 ^ g) → Fin (2 ^ b)) (σ : Fin (2 ^ g)) :
    (selectPauliUnitary g b (2 ^ g) (tblOf b g F)).1.mulVec
        (basisState (selectPauliDataEquiv g b (σ, 0))) =
      basisState (selectPauliDataEquiv g b (σ, F σ)) := by
  rw [selectPauliUnitary_mulVec_basisState g b (2 ^ g) (tblOf b g F) σ σ.2 0]
  have hcol : ∀ y : Fin (2 ^ b),
      (selectPauliTerm (tblOf b g F ⟨σ.val, σ.2⟩)).1 y 0 = if y = F σ then 1 else 0 := by
    intro y
    have := congrFun (tbl_col b g F σ) y
    rw [mulVec_basisState] at this
    rw [this, basisState_apply]
  simp only [hcol]
  rw [Finset.sum_eq_single (F σ)]
  · simp
  · intro y _ hy; simp [hy]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem zero_sum_eq (b g : ℕ) :
    ∑ γ : Fin g → ZMod 2, ket (extB b g g γ) =
      ∑ σ : Fin (2 ^ g), basisState (selectPauliDataEquiv g b (σ, 0)) := by
  refine Fintype.sum_equiv (basisBits g).symm _ _ (fun γ ↦ ?_)
  simp only [ket]
  congr 1
  apply (basisBits (b + g)).symm_apply_eq.2
  funext i
  rw [basisBits_dataEquiv g b]
  simp only [extB]
  by_cases h : i.val < b
  · rw [dif_pos h, dif_neg (by omega), basisBits_zero]; rfl
  · rw [dif_neg h, dif_pos ⟨by omega, by omega⟩]
    simp

theorem final_state (b g : ℕ) (F : Fin (2 ^ g) → Fin (2 ^ b)) :
    (selectPauliUnitary g b (2 ^ g) (tblOf b g F)).1.mulVec
        ((hPre b g g le_rfl).eval.1.mulVec (ket (0 : BitAssignment (b + g)))) =
      ((Real.sqrt (1 / 2) : ℂ) ^ g) •
        ∑ σ : Fin (2 ^ g), basisState (selectPauliDataEquiv g b (σ, F σ)) := by
  rw [hPre_ket, zero_sum_eq, Matrix.mulVec_smul, Matrix.mulVec_sum]
  simp only [sel_col]



open Finset Operator Matrix

theorem prob_formula (b g : ℕ) (F : Fin (2 ^ g) → Fin (2 ^ b)) (j : Fin (2 ^ b)) :
    prepareIndexProb b g (((Real.sqrt (1 / 2) : ℂ) ^ g) •
        ∑ σ : Fin (2 ^ g), basisState (selectPauliDataEquiv g b (σ, F σ))) j =
      ((univ.filter (fun σ ↦ F σ = j)).card : ℝ) / 2 ^ g := by
  unfold prepareIndexProb
  have hamp : ∀ x : Fin (2 ^ g),
      (((Real.sqrt (1 / 2) : ℂ) ^ g) •
        ∑ σ : Fin (2 ^ g), basisState (selectPauliDataEquiv g b (σ, F σ)))
          (prepareDataEquiv b g (j, x)) =
        ((Real.sqrt (1 / 2) : ℂ) ^ g) * (if F x = j then 1 else 0) := by
    intro x
    have he : prepareDataEquiv b g (j, x) = selectPauliDataEquiv g b (x, j) :=
      Fin.ext (by simp [prepareDataEquiv_val, selectPauliDataEquiv_val])
    rw [Pi.smul_apply, he, Finset.sum_apply, smul_eq_mul]
    congr 1
    simp only [basisState_apply]
    rw [Finset.sum_eq_single x]
    · by_cases h : F x = j
      · simp [h]
      · simp [h, (selectPauliDataEquiv g b).apply_eq_iff_eq]
        intro h'; exact absurd h'.symm h
    · intro σ _ hσ
      have : selectPauliDataEquiv g b (x, j) ≠ selectPauliDataEquiv g b (σ, F σ) := by
        intro h
        have := (selectPauliDataEquiv g b).injective h
        exact hσ (Prod.mk.inj this).1.symm
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hnorm : ∀ x : Fin (2 ^ g),
      ‖((Real.sqrt (1 / 2) : ℂ) ^ g) * (if F x = j then (1 : ℂ) else 0)‖ ^ 2 =
        (if F x = j then (1 / 2 : ℝ) ^ g else 0) := by
    intro x
    split_ifs
    · rw [mul_one, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
    · simp
  simp only [hamp, hnorm]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, one_div, inv_pow, div_eq_mul_inv, mul_comm]


theorem approx_state (b μ L : ℕ) (w : PrepareWeights L) (F : Fin (2 ^ (b + μ)) → Fin (2 ^ b))
    (hF1 : ∀ σ, (F σ).val < L)
    (hF2 : ∀ (j : Fin (2 ^ b)) (hj : j.val < L),
      |(((univ.filter (fun σ ↦ F σ = j)).card : ℝ) / 2 ^ (b + μ)) -
        ((w ⟨j.val, hj⟩ / prepareLambda w : ℚ) : ℝ)| ≤ 1 / (2 ^ μ * L)) :
    PrepareApproximates b (b + μ) L μ w (((Real.sqrt (1 / 2) : ℂ) ^ (b + μ)) •
        ∑ σ : Fin (2 ^ (b + μ)), basisState (selectPauliDataEquiv (b + μ) b (σ, F σ))) := by
  refine ⟨fun j hj ↦ ?_, fun j hj ↦ ?_⟩
  · rw [prob_formula]
    have : univ.filter (fun σ ↦ F σ = j) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun σ _ h ↦ ?_
      have := hF1 σ
      rw [h] at this
      omega
    rw [this]; simp
  · rw [prob_formula]
    exact hF2 j hj



open Finset Operator Matrix

theorem tblExt_self (g b : ℕ) (tbl : SelectPauliTable (2 ^ g) b) :
    tblExt g b (2 ^ g) tbl = tbl := by
  funext j
  simp only [tblExt, dif_pos j.2]

/-- The lookup circuit agrees with the embedded ideal `SELECT` unitary on the clean subspace,
as matrices. -/
theorem sel_clean (b g : ℕ) (tbl : SelectPauliTable (2 ^ g) b) {n : ℕ}
    (rData : QRegister (b + g) n) (rAnc : QRegister (g + 1) n) (hdisj : rData.DisjointWires rAnc) :
    ((mkWires rData rAnc hdisj.ne).full tbl).eval.1 * rAnc.basisOutcomeProjector 0 =
      (rData.embedUnitary (selectPauliUnitary g b (2 ^ g) tbl)).1 *
        rAnc.basisOutcomeProjector 0 := by
  apply matrix_ext_ket
  intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, basisOutcomeProjector_mulVec_ket]
  by_cases h0 : localIdx rAnc β = 0
  · rw [if_pos h0]
    have := hkey_main (le_refl (2 ^ g)) tbl rData rAnc hdisj β h0
    rwa [tblExt_self] at this
  · rw [if_neg h0, Matrix.mulVec_zero, Matrix.mulVec_zero]

theorem clean_key (b g : ℕ) (tbl : SelectPauliTable (2 ^ g) b) {n : ℕ}
    (rData : QRegister (b + g) n) (rAnc : QRegister (g + 1) n) (hdisj : rData.DisjointWires rAnc)
    (Hu : Unitary (2 ^ (b + g))) (β : BitAssignment n) (h0 : localIdx rAnc β = 0) :
    ((mkWires rData rAnc hdisj.ne).full tbl).eval.1.mulVec
        ((rData.embedUnitary Hu).1.mulVec (ket β)) =
      (rData.embedUnitary (selectPauliUnitary g b (2 ^ g) tbl)).1.mulVec
        ((rData.embedUnitary Hu).1.mulVec (ket β)) := by
  set Q0 := rAnc.basisOutcomeProjector 0 with hQ
  have hk : Q0.mulVec (ket β) = ket β := by
    rw [hQ, basisOutcomeProjector_mulVec_ket, if_pos h0]
  have hv : Q0.mulVec ((rData.embedUnitary Hu).1.mulVec (ket β)) =
      (rData.embedUnitary Hu).1.mulVec (ket β) := by
    rw [Matrix.mulVec_mulVec, CleanSubroutineBridge.embed_comm_proj rData rAnc hdisj Hu,
      ← Matrix.mulVec_mulVec, hk]
  have hs := sel_clean b g tbl rData rAnc hdisj
  calc _ = ((mkWires rData rAnc hdisj.ne).full tbl).eval.1.mulVec
          (Q0.mulVec ((rData.embedUnitary Hu).1.mulVec (ket β))) := by rw [hv]
    _ = (((mkWires rData rAnc hdisj.ne).full tbl).eval.1 * Q0).mulVec
          ((rData.embedUnitary Hu).1.mulVec (ket β)) := by rw [Matrix.mulVec_mulVec]
    _ = ((rData.embedUnitary (selectPauliUnitary g b (2 ^ g) tbl)).1 * Q0).mulVec
          ((rData.embedUnitary Hu).1.mulVec (ket β)) := by rw [hs]
    _ = _ := by rw [← Matrix.mulVec_mulVec, hv]

theorem realizes_prog {Var : Type} [DecidableEq Var] (b g : ℕ) (tbl : SelectPauliTable (2 ^ g) b)
    {n : ℕ} (rData : QRegister (b + g) n) (rAnc : QRegister (g + 1) n)
    (hdisj : rData.DisjointWires rAnc) :
    RealizesCleanSubroutine rData rAnc hdisj
      (selectPauliUnitary g b (2 ^ g) tbl * (hPre b g g le_rfl).eval)
      (DynamicCircuit.circuit (Var := Var) (Circuit.seq ((hPre b g g le_rfl).onRegister rData)
        ((mkWires rData rAnc hdisj.ne).full tbl))).compile := by
  refine CleanSubroutineBridge.realizesCleanSubroutine_of_lowerKraus_ket rData rAnc hdisj _
    (lowerKraus_circuit _) (fun β h0 ↦ ?_)
  rw [Circuit.eval_seq, Circuit.eval_onRegister, QRegister.embedUnitary_mul, mulVec_mul_unitary,
    mulVec_mul_unitary]
  exact clean_key b g tbl rData rAnc hdisj _ β h0



open Finset Operator Matrix

theorem count_hPre (b g t : ℕ) (ht : t ≤ g) {a : ℕ} (p : PrimitiveGate a)
    (hp : (⟨1, PrimitiveGate.H⟩ : Σ b, PrimitiveGate b) ≠ ⟨a, p⟩) :
    (hPre b g t ht).count p = 0 := by
  unfold hPre
  rw [Circuit.count_sequence, List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_eq_zero fun i _ ↦ Circuit.count_gate_of_ne _ _ _ hp

theorem count_prog (b g : ℕ) (tbl : SelectPauliTable (2 ^ g) b) {n : ℕ}
    (rData : QRegister (b + g) n) (rAnc : QRegister (g + 1) n)
    (hd : ∀ i j, rData i ≠ rAnc j) :
    (Circuit.seq ((hPre b g g le_rfl).onRegister rData)
        ((mkWires rData rAnc hd).full tbl)).count PrimitiveGate.TOFF = 0 ∧
      (Circuit.seq ((hPre b g g le_rfl).onRegister rData)
        ((mkWires rData rAnc hd).full tbl)).count PrimitiveGate.T ≤ 8 * g * 2 ^ g := by
  have h := (mkWires rData rAnc hd).count_full tbl
  rw [Circuit.count_seq, Circuit.count_seq, Circuit.count_onRegister, Circuit.count_onRegister,
    count_hPre b g g le_rfl _ (by simp), count_hPre b g g le_rfl _ (by simp)]
  exact ⟨by simpa using h.2, by simpa using h.1⟩



/-- Weight of the first `j` terms. -/
def cumW {L : ℕ} (w : PrepareWeights L) (j : ℕ) : ℚ :=
  ∑ i ∈ univ.filter (fun i : Fin L ↦ i.val < j), w i

/-- Threshold `C_j = ⌊2^(b+μ) (w_0 + ⋯ + w_{j-1}) / λ⌋` on the `2^(b+μ)` slots. -/
def thr (b L μ : ℕ) (w : PrepareWeights L) (j : ℕ) : ℕ :=
  ⌊(2 : ℚ) ^ (b + μ) * cumW w j / prepareLambda w⌋₊

/-- The classical fibre function of the weights `w`: slot `σ` is sent to the largest `j < L`
with `C_j ≤ σ`. -/
def pickF (b L μ : ℕ) (w : PrepareWeights L) : Fin (2 ^ (b + μ)) → Fin (2 ^ b) :=
  fun σ ↦ ⟨Nat.findGreatest (fun j ↦ thr b L μ w j ≤ σ.val) (L - 1) % 2 ^ b,
    Nat.mod_lt _ (by positivity)⟩

theorem cumW_zero {L : ℕ} (w : PrepareWeights L) : cumW w 0 = 0 := by
  simp [cumW]

theorem cumW_L {L : ℕ} (w : PrepareWeights L) : cumW w L = prepareLambda w := by
  unfold cumW prepareLambda
  rw [Finset.filter_true_of_mem fun i _ ↦ i.isLt]

theorem cumW_mono {L : ℕ} (w : PrepareWeights L) (hw : ∀ j, 0 ≤ w j) {j k : ℕ} (h : j ≤ k) :
    cumW w j ≤ cumW w k := by
  unfold cumW
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ ↦ hw i
  intro i hi
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  omega

theorem cumW_succ {L : ℕ} (w : PrepareWeights L) (j : ℕ) (hj : j < L) :
    cumW w (j + 1) = cumW w j + w ⟨j, hj⟩ := by
  unfold cumW
  rw [Finset.sum_filter, Finset.sum_filter]
  have : ∀ i : Fin L, (if i.val < j + 1 then w i else 0) =
      (if i.val < j then w i else 0) + (if i = ⟨j, hj⟩ then w i else 0) := by
    intro i
    by_cases h1 : i.val < j
    · have : i ≠ ⟨j, hj⟩ := fun h ↦ by simp [h] at h1
      simp only [h1, this, ite_true, ite_false, add_zero, show i.val < j + 1 from by omega]
    · by_cases h2 : i = ⟨j, hj⟩
      · subst h2; simp
      · have : ¬ i.val < j + 1 := fun h ↦ h2 (Fin.ext (by simp at h1 ⊢; omega))
        simp [h1, h2, this]
  rw [Finset.sum_congr rfl fun i _ ↦ this i, Finset.sum_add_distrib]
  simp

section Thr

variable {b L μ : ℕ} (w : PrepareWeights L)

theorem thr_zero : thr b L μ w 0 = 0 := by
  simp [thr, cumW_zero]

theorem thr_L (hsum : 0 < prepareLambda w) : thr b L μ w L = 2 ^ (b + μ) := by
  unfold thr
  rw [cumW_L, mul_div_assoc, div_self hsum.ne', mul_one]
  exact_mod_cast Nat.floor_natCast (2 ^ (b + μ))

theorem thr_mono (hw : ∀ j, 0 ≤ w j) (hsum : 0 < prepareLambda w) {j k : ℕ} (h : j ≤ k) :
    thr b L μ w j ≤ thr b L μ w k := by
  unfold thr
  refine Nat.floor_le_floor ?_
  have := cumW_mono w hw h
  gcongr


theorem fibre_iff (hLb : L ≤ 2 ^ b) (hw : ∀ j, 0 ≤ w j) (hsum : 0 < prepareLambda w)
    (σ : Fin (2 ^ (b + μ))) (j : Fin (2 ^ b)) (hj : j.val < L) :
    pickF b L μ w σ = j ↔ thr b L μ w j.val ≤ σ.val ∧ σ.val < thr b L μ w (j.val + 1) := by
  have hmL : Nat.findGreatest (fun j ↦ thr b L μ w j ≤ σ.val) (L - 1) ≤ L - 1 :=
    Nat.findGreatest_le _
  have hmb : Nat.findGreatest (fun j ↦ thr b L μ w j ≤ σ.val) (L - 1) < 2 ^ b := by omega
  have hσ := σ.isLt
  have hL := thr_L (b := b) (μ := μ) w hsum
  rw [Fin.ext_iff]
  simp only [pickF, Nat.mod_eq_of_lt hmb]
  rw [Nat.findGreatest_eq_iff]
  constructor
  · rintro ⟨-, h1, h2⟩
    refine ⟨?_, ?_⟩
    · by_cases h0 : j.val = 0
      · rw [h0, thr_zero]; exact Nat.zero_le _
      · exact h1 h0
    · by_cases hlast : j.val + 1 ≤ L - 1
      · exact not_le.1 (h2 (Nat.lt_succ_self _) hlast)
      · have : j.val + 1 = L := by omega
        rw [this, hL]; exact hσ
  · rintro ⟨h1, h2⟩
    refine ⟨by omega, fun h0 ↦ h1, fun n hn hnL hle ↦ ?_⟩
    have := thr_mono (b := b) (μ := μ) w hw hsum (show j.val + 1 ≤ n by omega)
    omega

theorem pickF_lt (hLb : L ≤ 2 ^ b) (hsum : 0 < prepareLambda w) (σ : Fin (2 ^ (b + μ))) :
    (pickF b L μ w σ).val < L := by
  have hL : 1 ≤ L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h; simp [prepareLambda] at hsum
    · exact h
  have hmL : Nat.findGreatest (fun j ↦ thr b L μ w j ≤ σ.val) (L - 1) ≤ L - 1 :=
    Nat.findGreatest_le _
  simp only [pickF, Nat.mod_eq_of_lt (show Nat.findGreatest (fun j ↦ thr b L μ w j ≤ σ.val)
    (L - 1) < 2 ^ b by omega)]
  omega


theorem fibre_card (hLb : L ≤ 2 ^ b) (hw : ∀ j, 0 ≤ w j) (hsum : 0 < prepareLambda w)
    (j : Fin (2 ^ b)) (hj : j.val < L) :
    (univ.filter (fun σ : Fin (2 ^ (b + μ)) ↦ pickF b L μ w σ = j)).card =
      thr b L μ w (j.val + 1) - thr b L μ w j.val := by
  have hc : thr b L μ w (j.val + 1) ≤ 2 ^ (b + μ) := by
    rw [← thr_L (b := b) (μ := μ) w hsum]
    exact thr_mono w hw hsum hj
  rw [← Nat.card_Ico]
  refine Finset.card_bij (fun σ _ ↦ σ.val) ?_ ?_ ?_
  · intro σ hσ
    have := (fibre_iff w hLb hw hsum σ j hj).1 (by simpa using hσ)
    simpa using this
  · intro σ _ τ _ h
    exact Fin.ext h
  · intro m hm
    rw [Finset.mem_Ico] at hm
    refine ⟨⟨m, by omega⟩, ?_, rfl⟩
    simpa using (fibre_iff w hLb hw hsum ⟨m, by omega⟩ j hj).2 hm

theorem fibre_bound (hLb : L ≤ 2 ^ b) (hw : ∀ j, 0 ≤ w j) (hsum : 0 < prepareLambda w)
    (j : Fin (2 ^ b)) (hj : j.val < L) :
    |(((univ.filter (fun σ : Fin (2 ^ (b + μ)) ↦ pickF b L μ w σ = j)).card : ℚ) / 2 ^ (b + μ)) -
        w ⟨j.val, hj⟩ / prepareLambda w| ≤ 1 / (2 ^ μ * L) := by
  have hc : thr b L μ w (j.val + 1) ≤ 2 ^ (b + μ) := by
    rw [← thr_L (b := b) (μ := μ) w hsum]
    exact thr_mono w hw hsum hj
  have hm : thr b L μ w j.val ≤ thr b L μ w (j.val + 1) := thr_mono w hw hsum (Nat.le_succ _)
  rw [fibre_card w hLb hw hsum j hj, Nat.cast_sub hm]
  set x : ℚ := (2 : ℚ) ^ (b + μ) * cumW w j.val / prepareLambda w with hx
  set y : ℚ := (2 : ℚ) ^ (b + μ) * cumW w (j.val + 1) / prepareLambda w with hy
  have hxy : y - x = (2 : ℚ) ^ (b + μ) * (w ⟨j.val, hj⟩ / prepareLambda w) := by
    rw [hx, hy, cumW_succ w j.val hj]; field_simp; ring
  have hxnn : 0 ≤ x := by
    rw [hx]; have : 0 ≤ cumW w j.val := by
      rw [← cumW_zero w]; exact cumW_mono w hw (Nat.zero_le _)
    positivity
  have hynn : 0 ≤ y := by
    rw [hy]; have : 0 ≤ cumW w (j.val + 1) := by
      rw [← cumW_zero w]; exact cumW_mono w hw (Nat.zero_le _)
    positivity
  have hx1 := Nat.floor_le hxnn
  have hx2 := Nat.lt_floor_add_one x
  have hy1 := Nat.floor_le hynn
  have hy2 := Nat.lt_floor_add_one y
  have hxf : thr b L μ w j.val = ⌊x⌋₊ := rfl
  have hyf : thr b L μ w (j.val + 1) = ⌊y⌋₊ := rfl
  rw [hxf, hyf] at *
  have hpos : (0 : ℚ) < 2 ^ (b + μ) := by positivity
  have hd : |((⌊y⌋₊ : ℚ) - ⌊x⌋₊) / 2 ^ (b + μ) - w ⟨j.val, hj⟩ / prepareLambda w| ≤
      1 / 2 ^ (b + μ) := by
    have e : ((⌊y⌋₊ : ℚ) - ⌊x⌋₊) / 2 ^ (b + μ) - w ⟨j.val, hj⟩ / prepareLambda w =
        (((⌊y⌋₊ : ℚ) - ⌊x⌋₊) - (y - x)) / 2 ^ (b + μ) := by
      rw [hxy]; field_simp
    rw [e, abs_div, abs_of_pos hpos]
    refine div_le_div_of_nonneg_right ?_ hpos.le
    rw [abs_le]; constructor <;> linarith
  refine hd.trans ?_
  have hL : (1 : ℚ) ≤ L := by
    have : 1 ≤ L := by
      rcases Nat.eq_zero_or_pos L with h | h
      · subst h; simp [prepareLambda] at hsum
      · exact h
    exact_mod_cast this
  have hLb' : (L : ℚ) ≤ 2 ^ b := by exact_mod_cast hLb
  rw [pow_add]
  refine one_div_le_one_div_of_le (by positivity) ?_
  nlinarith [pow_pos (show (0 : ℚ) < 2 by norm_num) μ]

end Thr

theorem approx_W (b μ L : ℕ) (w : PrepareWeights L) (F : Fin (2 ^ (b + μ)) → Fin (2 ^ b))
    (hF1 : ∀ σ, (F σ).val < L)
    (hF2 : ∀ (j : Fin (2 ^ b)) (hj : j.val < L),
      |(((univ.filter (fun σ ↦ F σ = j)).card : ℝ) / 2 ^ (b + μ)) -
        ((w ⟨j.val, hj⟩ / prepareLambda w : ℚ) : ℝ)| ≤ 1 / (2 ^ μ * L)) :
    PrepareApproximates b (b + μ) L μ w
      ((selectPauliUnitary (b + μ) b (2 ^ (b + μ)) (tblOf b (b + μ) F) *
        (hPre b (b + μ) (b + μ) le_rfl).eval).1.mulVec (basisState 0)) := by
  have hk : (basisState (0 : Fin (2 ^ (b + (b + μ)))) : Fin (2 ^ (b + (b + μ))) → ℂ) =
      ket 0 := by simp [ket]
  rw [mulVec_mul_unitary, hk, final_state]
  exact approx_state b μ L w F hF1 hF2

theorem pickF_spec (b L μ : ℕ) (hLb : L ≤ 2 ^ b) (w : PrepareWeights L) (hw : ∀ j, 0 ≤ w j)
    (hsum : 0 < prepareLambda w) :
    (∀ σ, (pickF b L μ w σ).val < L) ∧
      ∀ (j : Fin (2 ^ b)) (hj : j.val < L),
        |(((univ.filter (fun σ ↦ pickF b L μ w σ = j)).card : ℝ) / 2 ^ (b + μ)) -
            ((w ⟨j.val, hj⟩ / prepareLambda w : ℚ) : ℝ)| ≤ 1 / (2 ^ μ * L) := by
  refine ⟨pickF_lt w hLb hsum, fun j hj ↦ ?_⟩
  have h2 := (Rat.cast_le (K := ℝ)).2 (fibre_bound (μ := μ) w hLb hw hsum j hj)
  push_cast at h2 ⊢
  exact h2

end PrepareImpl

/-- Number of garbage qubits `prepareProgram` uses for `b` index qubits, `L` terms and precision
`μ`. Garbage starts in `|0⟩` and may end entangled with the index. It may not depend on the
weights. -/
def prepareGarbage (b L μ : ℕ) : ℕ := b + μ

/-- Number of clean ancilla qubits `prepareProgram` uses for `b` index qubits, `L` terms and
precision `μ`. It may not depend on the weights. -/
def prepareAncillas (b L μ : ℕ) : ℕ := b + μ + 1

/-- Candidate `PREPARE` circuit for the weights `w` on `b + prepareGarbage b L μ` data wires
`rData` (`b` index wires, least significant first, followed by the garbage wires) and
`prepareAncillas b L μ` clean ancilla wires `rAnc`. -/
def prepareProgram {n : ℕ} (b L μ : ℕ) (w : PrepareWeights L)
    (rData : QRegister (b + prepareGarbage b L μ) n)
    (rAnc : QRegister (prepareAncillas b L μ) n) : DynamicCircuit Var n :=
  if hd : ∀ i j, rData i ≠ rAnc j then
    .circuit (Circuit.seq ((PrepareImpl.hPre b (b + μ) (b + μ) le_rfl).onRegister rData)
      ((SelectPauliImpl.mkWires (b := b + μ) (N := b) rData rAnc hd).full
        (PrepareImpl.tblOf b (b + μ) (PrepareImpl.pickF b L μ w))))
  else .circuit .identity

theorem prepareProgram_count {n : ℕ} (b L μ : ℕ) (w : PrepareWeights L)
    (rData : QRegister (b + prepareGarbage b L μ) n)
    (rAnc : QRegister (prepareAncillas b L μ) n) :
    (prepareProgram b L μ w rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (prepareProgram b L μ w rData rAnc).count PrimitiveGate.T ≤ 8 * (b + μ) * 2 ^ (b + μ) := by
  by_cases hd' : ∀ i j, rData i ≠ rAnc j
  · have hprog : prepareProgram b L μ w rData rAnc =
        .circuit (Circuit.seq ((PrepareImpl.hPre b (b + μ) (b + μ) le_rfl).onRegister rData)
          ((SelectPauliImpl.mkWires (b := b + μ) (N := b) rData rAnc hd').full
            (PrepareImpl.tblOf b (b + μ) (PrepareImpl.pickF b L μ w)))) := by
      unfold prepareProgram
      rw [dif_pos hd']
    simp only [hprog, DynamicCircuit.count]
    exact PrepareImpl.count_prog b (b + μ) _ rData rAnc hd'
  · have hprog : prepareProgram b L μ w rData rAnc = .circuit .identity := by
      unfold prepareProgram
      rw [dif_neg hd']
    simp only [hprog, DynamicCircuit.count]
    exact ⟨rfl, Nat.zero_le _⟩

/-- For all `b`, `1 ≤ L ≤ 2^b`, `μ` and every weight table with `w_j ≥ 0` and `λ > 0`, there is
a unitary `W` on index plus garbage such that `W |0⟩` has index probabilities `0` on `j ≥ L` and
within `1 / (2^μ L)` of `w_j / λ` on `j < L`, and `prepareProgram` acts as `W` on every
input of index plus garbage when the ancillas start in zero, returning the ancillas to zero,
across all disjoint register placements. In particular it maps the all-zero input to the pure
state `W |0⟩ ⊗ |0⟩`. -/
theorem prepare_correctness (b L μ : ℕ) (hL : 1 ≤ L) (hLb : L ≤ 2 ^ b)
    (w : PrepareWeights L) (hw : ∀ j, 0 ≤ w j) (hsum : 0 < prepareLambda w) :
    ∃ W : Unitary (2 ^ (b + prepareGarbage b L μ)),
      PrepareApproximates b (prepareGarbage b L μ) L μ w (W.1 *ᵥ basisState 0) ∧
      ∀ {n : ℕ}
        (rData : QRegister (b + prepareGarbage b L μ) n)
        (rAnc : QRegister (prepareAncillas b L μ) n)
        (hdisj : rData.DisjointWires rAnc),
        RealizesCleanSubroutine rData rAnc hdisj W
          (prepareProgram b L μ w rData rAnc).compile := by
  obtain ⟨hF1, hF2⟩ := PrepareImpl.pickF_spec b L μ hLb w hw hsum
  refine ⟨selectPauliUnitary (b + μ) b (2 ^ (b + μ))
      (PrepareImpl.tblOf b (b + μ) (PrepareImpl.pickF b L μ w)) *
        (PrepareImpl.hPre b (b + μ) (b + μ) le_rfl).eval, ?_, ?_⟩
  · exact PrepareImpl.approx_W b μ L w _ hF1 hF2
  · intro n rData rAnc hdisj
    have hd' : ∀ i j, rData i ≠ rAnc j := fun i j ↦ hdisj.ne i j
    have hprog : prepareProgram b L μ w rData rAnc =
        .circuit (Circuit.seq ((PrepareImpl.hPre b (b + μ) (b + μ) le_rfl).onRegister rData)
          ((SelectPauliImpl.mkWires (b := b + μ) (N := b) rData rAnc hd').full
            (PrepareImpl.tblOf b (b + μ) (PrepareImpl.pickF b L μ w)))) := by
      unfold prepareProgram
      rw [dif_pos hd']
    rw [hprog]
    exact PrepareImpl.realizes_prog b (b + μ) _ rData rAnc hdisj

/-- `T`-gate count of `prepareProgram`. -/
abbrev prepareTCount {n : ℕ} (b L μ : ℕ) (w : PrepareWeights L)
    (rData : QRegister (b + prepareGarbage b L μ) n)
    (rAnc : QRegister (prepareAncillas b L μ) n) : ℕ :=
  (prepareProgram b L μ w rData rAnc).count PrimitiveGate.T

/-- Declared qubits: `b` index qubits, `prepareGarbage b L μ` garbage qubits and
`prepareAncillas b L μ` clean ancillas. -/
abbrev prepareQubits (b L μ : ℕ) : ℕ :=
  b + prepareGarbage b L μ + prepareAncillas b L μ

/-!
## `T`-Count Cost Theorem

The cost theorem forbids primitive `TOFF` gates and bounds the `T` count by the claimed
`prepareTCost b L μ`, for all sizes, every valid weight table and every register placement.
-/

/-- Claimed `T` count of `prepareProgram` for `b` index qubits, `L` terms and precision `μ`. It
depends only on `(b, L, μ)`. -/
def prepareTCost (b L μ : ℕ) : ℕ := 8 * (b + μ) * 2 ^ (b + μ)

/-- For all `b`, `1 ≤ L ≤ 2^b`, `μ`, every weight table with `w_j ≥ 0` and `λ > 0`, and every
register placement, `prepareProgram` uses no `TOFF` gates and at most `prepareTCost b L μ` `T`
gates. -/
theorem prepare_t_cost (b L μ : ℕ) (hL : 1 ≤ L) (hLb : L ≤ 2 ^ b)
    (w : PrepareWeights L) (hw : ∀ j, 0 ≤ w j) (hsum : 0 < prepareLambda w) {n : ℕ}
    (rData : QRegister (b + prepareGarbage b L μ) n)
    (rAnc : QRegister (prepareAncillas b L μ) n) :
    (prepareProgram b L μ w rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      prepareTCount b L μ w rData rAnc ≤ prepareTCost b L μ := by
  have h := prepareProgram_count b L μ w rData rAnc
  exact ⟨h.1, h.2⟩

/-!
## Spacetime Cost Theorem at the Pinned Size

The cost theorem forbids primitive `TOFF` gates and bounds `T count * qubits` by a closed `ℕ`
constant at `PrepareSize.b4mu8` (`b = 4` index qubits, `L = 16 = 2^b` terms, `μ = 8`), for every
weight table with `w_j ≥ 0` and `λ > 0` and every register placement.
-/

/-- Sizes of a `PREPARE` instance: `b` index qubits, `L` terms, precision `μ`. -/
structure PrepareSize where
  /-- Number of index qubits. -/
  b : ℕ
  /-- Number of terms. -/
  L : ℕ
  /-- Precision of the keep values. -/
  μ : ℕ

/-- The pinned size `b = 4`, `L = 16`, `μ = 8`. -/
abbrev PrepareSize.b4mu8 : PrepareSize where
  b := 4
  L := 16
  μ := 8

/-- Claimed spacetime cost (`T count * qubits`) of `prepareProgram` at `PrepareSize.b4mu8`. -/
def prepareB4Mu8SpacetimeCost : ℕ := 11403264

/-- At `PrepareSize.b4mu8`, for every weight table with `w_j ≥ 0` and `λ > 0` and every register
placement, `prepareProgram` uses no `TOFF` gates and has `T count * (b + garbage + ancillas)` at
most `prepareB4Mu8SpacetimeCost`. -/
theorem prepare_b4mu8_spacetime_cost
    (w : PrepareWeights PrepareSize.b4mu8.L) (hw : ∀ j, 0 ≤ w j) (hsum : 0 < prepareLambda w)
    {n : ℕ}
    (rData : QRegister (PrepareSize.b4mu8.b +
      prepareGarbage PrepareSize.b4mu8.b PrepareSize.b4mu8.L PrepareSize.b4mu8.μ) n)
    (rAnc : QRegister (prepareAncillas PrepareSize.b4mu8.b PrepareSize.b4mu8.L
      PrepareSize.b4mu8.μ) n) :
    (prepareProgram PrepareSize.b4mu8.b PrepareSize.b4mu8.L PrepareSize.b4mu8.μ w rData
        rAnc).count PrimitiveGate.TOFF = 0 ∧
      prepareTCount PrepareSize.b4mu8.b PrepareSize.b4mu8.L PrepareSize.b4mu8.μ w rData rAnc *
        prepareQubits PrepareSize.b4mu8.b PrepareSize.b4mu8.L PrepareSize.b4mu8.μ ≤
      prepareB4Mu8SpacetimeCost := by
  have h := prepareProgram_count PrepareSize.b4mu8.b PrepareSize.b4mu8.L
    PrepareSize.b4mu8.μ w rData rAnc
  refine ⟨h.1, ?_⟩
  have h2 : prepareTCount PrepareSize.b4mu8.b PrepareSize.b4mu8.L PrepareSize.b4mu8.μ w
      rData rAnc ≤ 393216 := h.2.trans (by norm_num)
  have h3 : prepareQubits PrepareSize.b4mu8.b PrepareSize.b4mu8.L PrepareSize.b4mu8.μ = 29 := by
    norm_num [prepareQubits, prepareGarbage, prepareAncillas]
  rw [h3]
  calc _ ≤ 393216 * 29 := Nat.mul_le_mul_right 29 h2
    _ = prepareB4Mu8SpacetimeCost := by norm_num [prepareB4Mu8SpacetimeCost]

/-! ## The ℕ-valued holes at the pinned sizes -/

example : prepareGarbage 4 16 8 = 12 := rfl
example : prepareAncillas 4 16 8 = 13 := rfl
example : prepareTCost 4 16 8 = 393216 := rfl
example : prepareB4Mu8SpacetimeCost = 11403264 := rfl

end QuantumComputation.Specs
