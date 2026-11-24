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

/-
This file is a solution to the specification `QuantumSpecs/BlockEncoding/PreparePauliLCU.lean` (sha256 af0f6e35...):
the spec with its five holes filled and its three theorems proved, for alias-sampling `PREPARE`
(Babbush et al., arXiv:1805.03662, Section III.D) with a coherent alias table.

The section between the markers `BEGIN GOOGLE-DERIVED` and `END GOOGLE-DERIVED` is copied
(through this repository's `QuantumSolutions/Lookup/TableLookup.lean`, lines 82 to 2425) from
google-deepmind/formal-quantum-computation, branch `discoveries` (commit a88de8f, 2026-11-17), files
`QuantumComputationDiscoveries/Primitives/Arcsin/Solution/{LowerKraus,StepSemantics,
EqualTableAdd}.lean`, Copyright 2026 Google LLC, licensed under the Apache License, Version 2.0.
Modification: the namespace `ArcsinImpl` is renamed to `TableLookupSteps`. Nothing else changed.
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

/-! BEGIN GOOGLE-DERIVED (LowerKraus.lean) -/

namespace QuantumComputation.Specs

namespace TableLookupSteps

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


inductive Step (n : ℕ) : Type where
  | x (q : Wire n)
  | cnot (c t : Wire n)
  | and4t (c₁ c₂ t : Wire n)
  | rccx0 (c₁ c₂ t : Wire n)
  | rccx1 (c₁ c₂ t : Wire n)
  | unand (c₁ c₂ t : Wire n)
  | unxorList (sources : List (Wire n)) (t : Wire n)
  | unquad (quads : List (Wire n × Wire n)) (lins : List (Wire n)) (t : Wire n)


end TableLookupSteps

end QuantumComputation.Specs

/-! BEGIN GOOGLE-DERIVED (StepSemantics.lean) -/

namespace QuantumComputation.Specs

namespace TableLookupSteps

open Operator Matrix QProg Function
open scoped Matrix ComplexOrder MatrixOrder

variable {Var : Type} {n : ℕ}

namespace Step

def NoUnxor : Step n → Prop
  | unxorList _ _ => False
  | unquad _ _ _ => False
  | rccx0 _ _ _ => False
  | rccx1 _ _ _ => False
  | _ => True

def run : Step n → BitAssignment n → Option (BitAssignment n)
  | x q, β => some (update β q (β q + 1))
  | cnot c t, β => if c ≠ t then some (update β t (β t + β c)) else some β
  | and4t c₁ c₂ t, β =>
      if c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then
        if β t = 0 then some (update β t (β c₁ * β c₂)) else none
      else some β
  | rccx0 c₁ c₂ t, β =>
      if c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then
        if β c₁ * β c₂ * β t = 0 then some (update β t (β t + β c₁ * β c₂)) else none
      else some β
  | rccx1 c₁ c₂ t, β =>
      if c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then
        if β c₁ * β c₂ * (β t + 1) = 0 then some (update β t (β t + β c₁ * β c₂)) else none
      else some β
  | unand c₁ c₂ t, β =>
      if c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then
        if β t = β c₁ * β c₂ then some (update β t 0) else none
      else some β
  | unxorList sources t, β =>
      if t ∉ sources then
        if β t = (sources.map β).sum then some (update β t 0) else none
      else some β
  | unquad quads lins t, β =>
      if (∀ p ∈ quads, p.1 ≠ p.2 ∧ p.1 ≠ t ∧ p.2 ≠ t) ∧ t ∉ lins then
        if β t = (quads.map (fun p ↦ β p.1 * β p.2)).sum + (lins.map β).sum then
          some (update β t 0)
        else none
      else some β

def rawRun : Step n → BitAssignment n → Option (BitAssignment n)
  | x q, β => some (update β q (β q + 1))
  | cnot c t, β => if c ≠ t then some (update β t (β t + β c)) else some β
  | and4t c₁ c₂ t, β =>
      if c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then some (update β t (β t + β c₁ * β c₂)) else some β
  | rccx0 c₁ c₂ t, β =>
      if c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then some (update β t (β t + β c₁ * β c₂)) else some β
  | rccx1 c₁ c₂ t, β =>
      if c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then some (update β t (β t + β c₁ * β c₂)) else some β
  | unand c₁ c₂ t, β =>
      if c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then
        if β t = β c₁ * β c₂ then some (update β t 0) else none
      else some β
  | unxorList sources t, β =>
      if t ∉ sources then
        if β t = (sources.map β).sum then some (update β t 0) else none
      else some β
  | unquad quads lins t, β =>
      if (∀ p ∈ quads, p.1 ≠ p.2 ∧ p.1 ≠ t ∧ p.2 ≠ t) ∧ t ∉ lins then
        if β t = (quads.map (fun p ↦ β p.1 * β p.2)).sum + (lins.map β).sum then
          some (update β t 0)
        else none
      else some β

def inv : Step n → Step n
  | x q => x q
  | cnot c t => cnot c t
  | and4t c₁ c₂ t => unand c₁ c₂ t
  | rccx0 c₁ c₂ t => rccx1 c₁ c₂ t
  | rccx1 c₁ c₂ t => rccx0 c₁ c₂ t
  | unand c₁ c₂ t => and4t c₁ c₂ t
  | unxorList sources t => unxorList sources t
  | unquad quads lins t => unquad quads lins t

def compile (v : Var) : Step n → DynamicCircuit Var n
  | x q => .circuit (Circuit.X q)
  | cnot c t => if h : c ≠ t then .circuit (Circuit.CNOT c t h) else .identity
  | and4t c₁ c₂ t =>
      if h : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then .circuit (AND4T c₁ c₂ t h.1 h.2.1 h.2.2)
      else .identity
  | rccx0 c₁ c₂ t =>
      if h : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then .circuit (RCCX0 c₁ c₂ t h.1 h.2.1 h.2.2)
      else .identity
  | rccx1 c₁ c₂ t =>
      if h : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then .circuit (RCCX1 c₁ c₂ t h.1 h.2.1 h.2.2)
      else .identity
  | unand c₁ c₂ t =>
      if h : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then
        .seq (.circuit (Circuit.H t)) (.seq (.measure v (QRegister.singleton t))
          (.qIf (fun σ ↦ σ v = 1) (.circuit (fixup c₁ c₂ t h.1)) .identity))
      else .identity
  | unxorList sources t =>
      if _ : t ∉ sources then
        .seq (.circuit (Circuit.H t)) (.seq (.measure v (QRegister.singleton t))
          (.qIf (fun σ ↦ σ v = 1) (.circuit (fixupZ sources t)) .identity))
      else .identity
  | unquad quads lins t =>
      if _ : (∀ p ∈ quads, p.1 ≠ p.2 ∧ p.1 ≠ t ∧ p.2 ≠ t) ∧ t ∉ lins then
        .seq (.circuit (Circuit.H t)) (.seq (.measure v (QRegister.singleton t))
          (.qIf (fun σ ↦ σ v = 1) (.circuit (fixupQuad quads lins t)) .identity))
      else .identity

def andCount : Step n → ℕ
  | and4t _ _ _ => 1
  | rccx0 _ _ _ => 1
  | rccx1 _ _ _ => 1
  | _ => 0

theorem eq_of_update_eq {β β' : BitAssignment n} {q : Wire n} {a a' : ZMod 2}
    (h : update β q a = update β' q a') (hq : β q = β' q) : β = β' := by
  funext w
  by_cases hw : w = q
  · subst hw
    exact hq
  · simpa [update_of_ne hw] using congrFun h w

theorem update_apply_eq {β β' : BitAssignment n} {q w : Wire n} {a a' : ZMod 2}
    (h : update β q a = update β' q a') (hw : w ≠ q) : β w = β' w := by
  simpa [update_of_ne hw] using congrFun h w

theorem rawRun_of_run {s : Step n} {β γ : BitAssignment n} (h : s.run β = some γ) :
    s.rawRun β = some γ := by
  cases s with
  | x _ => exact h
  | cnot _ _ => exact h
  | unand _ _ _ => exact h
  | unxorList _ _ => exact h
  | unquad _ _ _ => exact h
  | and4t c₁ c₂ t =>
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
    · simp only [run, rawRun, ite_eq_left hd] at h ⊢
      split_ifs at h with ht0
      simp only [Option.some.injEq] at h ⊢
      rw [← h, ht0, zero_add]
    · simp only [run, rawRun, ite_eq_right hd] at h ⊢
      exact h
  | rccx0 c₁ c₂ t =>
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
    · simp only [run, rawRun, ite_eq_left hd] at h ⊢
      split_ifs at h with ht0
      exact h
    · simp only [run, rawRun, ite_eq_right hd] at h ⊢
      exact h
  | rccx1 c₁ c₂ t =>
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
    · simp only [run, rawRun, ite_eq_left hd] at h ⊢
      split_ifs at h with ht0
      exact h
    · simp only [run, rawRun, ite_eq_right hd] at h ⊢
      exact h

theorem rawRun_injective {s : Step n} {β β' γ : BitAssignment n} (h : s.rawRun β = some γ)
    (h' : s.rawRun β' = some γ) : β = β' := by
  cases s with
  | x q =>
    simp only [rawRun, Option.some.injEq] at h h'
    rw [← h'] at h
    exact eq_of_update_eq h (by simpa using congrFun h q)
  | cnot c t =>
    by_cases hd : c ≠ t
    · simp only [rawRun, ite_eq_left hd, Option.some.injEq] at h h'
      rw [← h'] at h
      have hc := update_apply_eq h hd
      exact eq_of_update_eq h (by simpa [hc] using congrFun h t)
    · simp only [rawRun, ite_eq_right hd, Option.some.injEq] at h h'
      exact h.trans h'.symm
  | and4t c₁ c₂ t =>
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
    · simp only [rawRun, ite_eq_left hd, Option.some.injEq] at h h'
      rw [← h'] at h
      have hc₁ := update_apply_eq h hd.2.1
      have hc₂ := update_apply_eq h hd.2.2
      exact eq_of_update_eq h (by simpa [hc₁, hc₂] using congrFun h t)
    · simp only [rawRun, ite_eq_right hd, Option.some.injEq] at h h'
      exact h.trans h'.symm
  | rccx0 c₁ c₂ t =>
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
    · simp only [rawRun, ite_eq_left hd, Option.some.injEq] at h h'
      rw [← h'] at h
      have hc₁ := update_apply_eq h hd.2.1
      have hc₂ := update_apply_eq h hd.2.2
      exact eq_of_update_eq h (by simpa [hc₁, hc₂] using congrFun h t)
    · simp only [rawRun, ite_eq_right hd, Option.some.injEq] at h h'
      exact h.trans h'.symm
  | rccx1 c₁ c₂ t =>
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
    · simp only [rawRun, ite_eq_left hd, Option.some.injEq] at h h'
      rw [← h'] at h
      have hc₁ := update_apply_eq h hd.2.1
      have hc₂ := update_apply_eq h hd.2.2
      exact eq_of_update_eq h (by simpa [hc₁, hc₂] using congrFun h t)
    · simp only [rawRun, ite_eq_right hd, Option.some.injEq] at h h'
      exact h.trans h'.symm
  | unand c₁ c₂ t =>
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
    · simp only [rawRun, ite_eq_left hd] at h h'
      split_ifs at h h' with ht ht'
      simp only [Option.some.injEq] at h h'
      rw [← h'] at h
      have hc₁ := update_apply_eq h hd.2.1
      have hc₂ := update_apply_eq h hd.2.2
      exact eq_of_update_eq h (by rw [ht, ht', hc₁, hc₂])
    · simp only [rawRun, ite_eq_right hd, Option.some.injEq] at h h'
      exact h.trans h'.symm
  | unxorList sources t =>
    by_cases hd : t ∉ sources
    · simp only [rawRun, ite_eq_left hd] at h h'
      split_ifs at h h' with ht ht'
      simp only [Option.some.injEq] at h h'
      rw [← h'] at h
      have hmap : sources.map β = sources.map β' :=
        List.map_congr_left fun c hc ↦ update_apply_eq h (fun eq ↦ hd (eq ▸ hc))
      exact eq_of_update_eq h (by rw [ht, ht', hmap])
    · simp only [rawRun, ite_eq_right hd, Option.some.injEq] at h h'
      exact h.trans h'.symm
  | unquad quads lins t =>
    by_cases hd : (∀ p ∈ quads, p.1 ≠ p.2 ∧ p.1 ≠ t ∧ p.2 ≠ t) ∧ t ∉ lins
    · simp only [rawRun, ite_eq_left hd] at h h'
      split_ifs at h h' with ht ht'
      simp only [Option.some.injEq] at h h'
      rw [← h'] at h
      have hqmap : quads.map (fun p ↦ β p.1 * β p.2) = quads.map (fun p ↦ β' p.1 * β' p.2) :=
        List.map_congr_left fun p hp ↦ by
          rw [update_apply_eq h (hd.1 p hp).2.1, update_apply_eq h (hd.1 p hp).2.2]
      have hlmap : lins.map β = lins.map β' :=
        List.map_congr_left fun c hc ↦ update_apply_eq h (fun eq ↦ hd.2 (eq ▸ hc))
      exact eq_of_update_eq h (by rw [ht, ht', hqmap, hlmap])
    · simp only [rawRun, ite_eq_right hd, Option.some.injEq] at h h'
      exact h.trans h'.symm

theorem count_T_compile (v : Var) (s : Step n) :
    (s.compile v).count PrimitiveGate.T ≤ 4 * s.andCount := by
  cases s <;> simp [compile, andCount] <;> split_ifs <;>
    simp [fixup, count_T_AND4T, count_T_RCCX0, count_T_RCCX1, count_T_fixupZ, count_T_fixupQuad]

theorem count_TOFF_compile (v : Var) (s : Step n) :
    (s.compile v).count PrimitiveGate.TOFF = 0 := by
  cases s <;> simp [compile] <;> split_ifs <;>
    simp [fixup, count_TOFF_AND4T, count_TOFF_RCCX0, count_TOFF_RCCX1, count_TOFF_fixupZ,
      count_TOFF_fixupQuad]

theorem unand_scalar (a b : ZMod 2) (ψ : Fin (2 ^ n) → ℂ) :
    sqrtHalf • (sqrtHalf • ψ + bitSign a • sqrtHalf • bitSign b • ψ) =
      if a = b then ψ else 0 := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    simp only [bitSign, one_ne_zero, zero_ne_one, ↓reduceIte, one_smul, neg_smul, smul_neg,
      smul_add, smul_smul] <;> match_scalars <;>
    first
      | linear_combination 2 * sqrtHalf_mul_sqrtHalf
      | linear_combination 0 * sqrtHalf_mul_sqrtHalf

theorem exists_lowerKraus [DecidableEq Var] [NeZero (2 ^ n)] (v : Var)
    (s : Step n) :
    ∃ R, LowerKraus (s.compile v).compile R ∧
      (∀ β γ, s.run β = some γ → R.mulVec (ket β) = ket γ) ∧
      (∀ β, ∃ z : ℂ, R.mulVec (ket β) = z • optKet (s.rawRun β)) := by
  cases s with
  | x q =>
    refine ⟨_, lowerKraus_circuit _, ?_, fun β ↦ ⟨1, by rw [one_smul, rawRun, optKet, ket_X]⟩⟩
    intro β γ h
    simp only [run, Option.some.injEq] at h
    rw [← h, ket_X]
  | cnot c t =>
    by_cases hd : c ≠ t
    · simp only [compile, dite_eq_left hd, run, rawRun, ite_eq_left hd, optKet]
      refine ⟨_, lowerKraus_circuit _, ?_, fun β ↦ ⟨1, by rw [one_smul, ket_CNOT c t hd β]⟩⟩
      intro β γ h
      simp only [Option.some.injEq] at h
      rw [← h, ket_CNOT]
    · simp only [compile, dite_eq_right hd, run, rawRun, ite_eq_right hd, optKet]
      refine ⟨1, lowerKraus_skip, ?_, fun β ↦ ⟨1, by rw [one_smul, Matrix.one_mulVec]⟩⟩
      intro β γ h
      simp only [Option.some.injEq] at h
      rw [← h, Matrix.one_mulVec]
  | and4t c₁ c₂ t =>
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
    · simp only [compile, dite_eq_left hd, run, rawRun, ite_eq_left hd, optKet]
      refine ⟨_, lowerKraus_circuit _, ?_, ?_⟩
      · intro β γ h
        split_ifs at h with ht0
        simp only [Option.some.injEq] at h
        simp only [← h, ket_AND4T_eq_smul, ht0, cleanAndPhase, ↓reduceIte, one_smul, zero_add]
      · intro β
        exact ⟨cleanAndPhase (β c₁) (β c₂) (β t),
          ket_AND4T_eq_smul c₁ c₂ t hd.1 hd.2.1 hd.2.2 β⟩
    · simp only [compile, dite_eq_right hd, run, rawRun, ite_eq_right hd, optKet]
      refine ⟨1, lowerKraus_skip, ?_, fun β ↦ ⟨1, by rw [one_smul, Matrix.one_mulVec]⟩⟩
      intro β γ h
      simp only [Option.some.injEq] at h
      rw [← h, Matrix.one_mulVec]
  | rccx0 c₁ c₂ t =>
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
    · simp only [compile, dite_eq_left hd, run, rawRun, ite_eq_left hd, optKet]
      refine ⟨_, lowerKraus_circuit _, ?_, ?_⟩
      · intro β γ h
        split_ifs at h with ht0
        simp only [Option.some.injEq] at h
        rw [← h, ket_RCCX0_eq_smul, rccx0Phase_eq_one ht0, one_smul]
      · intro β
        exact ⟨rccx0Phase (β c₁) (β c₂) (β t),
          ket_RCCX0_eq_smul c₁ c₂ t hd.1 hd.2.1 hd.2.2 β⟩
    · simp only [compile, dite_eq_right hd, run, rawRun, ite_eq_right hd, optKet]
      refine ⟨1, lowerKraus_skip, ?_, fun β ↦ ⟨1, by rw [one_smul, Matrix.one_mulVec]⟩⟩
      intro β γ h
      simp only [Option.some.injEq] at h
      rw [← h, Matrix.one_mulVec]
  | rccx1 c₁ c₂ t =>
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
    · simp only [compile, dite_eq_left hd, run, rawRun, ite_eq_left hd, optKet]
      refine ⟨_, lowerKraus_circuit _, ?_, ?_⟩
      · intro β γ h
        split_ifs at h with ht0
        simp only [Option.some.injEq] at h
        rw [← h, ket_RCCX1_eq_smul, rccx0Phase_eq_one ht0, one_smul]
      · intro β
        exact ⟨rccx0Phase (β c₁) (β c₂) (β t + 1),
          ket_RCCX1_eq_smul c₁ c₂ t hd.1 hd.2.1 hd.2.2 β⟩
    · simp only [compile, dite_eq_right hd, run, rawRun, ite_eq_right hd, optKet]
      refine ⟨1, lowerKraus_skip, ?_, fun β ↦ ⟨1, by rw [one_smul, Matrix.one_mulVec]⟩⟩
      intro β γ h
      simp only [Option.some.injEq] at h
      rw [← h, Matrix.one_mulVec]
  | unand c₁ c₂ t =>
    by_cases hd : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
    · simp only [compile, dite_eq_left hd, run, rawRun, ite_eq_left hd]
      have hmain : ∀ β,
          ((sqrtHalf • ((QRegister.singleton t).basisOutcomeProjector 0 +
            (fixup c₁ c₂ t hd.1).eval.1 * (QRegister.singleton t).basisOutcomeProjector 1)) *
            (Circuit.H t).eval.1).mulVec (ket β) =
          optKet (if β t = β c₁ * β c₂ then some (update β t 0) else none) := by
        intro β
        have hH : (Circuit.H t).eval.1.mulVec (ket β) =
            sqrtHalf • (ket (update β t 0) + bitSign (β t) • ket (update β t 1)) := ket_H t β
        have hF : (fixup c₁ c₂ t hd.1).eval.1.mulVec (ket (update β t 1)) =
            bitSign (β c₁ * β c₂) • ket (update β t 0) := by
          rw [fixup_mulVec_ket, update_of_ne hd.2.1, update_of_ne hd.2.2, update_self, update_idem,
            one_add_one_zmod2]
        simp only [← Matrix.mulVec_mulVec, hH, Matrix.mulVec_smul, Matrix.smul_mulVec,
          Matrix.add_mulVec, Matrix.mulVec_add, ket_projector_zero, ket_projector_one, update_self,
          hF, ↓reduceIte, one_ne_zero, zero_ne_one, Matrix.mulVec_zero, add_zero, zero_add]
        rw [unand_scalar]
        split_ifs <;> rfl
      refine ⟨_, (lowerKraus_circuit (Circuit.H t)).qSeq
        (lowerKraus_measure_singleton_qIf v t (lowerKraus_circuit (fixup c₁ c₂ t hd.1))),
        ?_, fun β ↦ ⟨1, by rw [one_smul, hmain]⟩⟩
      intro β γ h
      rw [hmain, h, optKet]
    · simp only [compile, dite_eq_right hd, run, rawRun, ite_eq_right hd, optKet]
      refine ⟨1, lowerKraus_skip, ?_, fun β ↦ ⟨1, by rw [one_smul, Matrix.one_mulVec]⟩⟩
      intro β γ h
      simp only [Option.some.injEq] at h
      rw [← h, Matrix.one_mulVec]
  | unxorList sources t =>
    by_cases hd : t ∉ sources
    · simp only [compile, dite_eq_left hd, run, rawRun, ite_eq_left hd]
      have hmain : ∀ β,
          ((sqrtHalf • ((QRegister.singleton t).basisOutcomeProjector 0 +
            (fixupZ sources t).eval.1 * (QRegister.singleton t).basisOutcomeProjector 1)) *
            (Circuit.H t).eval.1).mulVec (ket β) =
          optKet (if β t = (sources.map β).sum then some (update β t 0) else none) := by
        intro β
        have hH : (Circuit.H t).eval.1.mulVec (ket β) =
            sqrtHalf • (ket (update β t 0) + bitSign (β t) • ket (update β t 1)) := ket_H t β
        have hmap : sources.map (update β t 1) = sources.map β :=
          List.map_congr_left fun c hc ↦ update_of_ne (fun eq : c = t ↦ hd (eq ▸ hc)) _ _
        have hF : (fixupZ sources t).eval.1.mulVec (ket (update β t 1)) =
            bitSign ((sources.map β).sum) • ket (update β t 0) := by
          rw [fixupZ_mulVec_ket, hmap, update_self, update_idem, one_add_one_zmod2]
        simp only [← Matrix.mulVec_mulVec, hH, Matrix.mulVec_smul, Matrix.smul_mulVec,
          Matrix.add_mulVec, Matrix.mulVec_add, ket_projector_zero, ket_projector_one, update_self,
          hF, ↓reduceIte, one_ne_zero, zero_ne_one, Matrix.mulVec_zero, add_zero, zero_add]
        rw [unand_scalar]
        split_ifs <;> rfl
      refine ⟨_, (lowerKraus_circuit (Circuit.H t)).qSeq
        (lowerKraus_measure_singleton_qIf v t (lowerKraus_circuit (fixupZ sources t))),
        ?_, fun β ↦ ⟨1, by rw [one_smul, hmain]⟩⟩
      intro β γ h
      rw [hmain, h, optKet]
    · simp only [compile, dite_eq_right hd, run, rawRun, ite_eq_right hd, optKet]
      refine ⟨1, lowerKraus_skip, ?_, fun β ↦ ⟨1, by rw [one_smul, Matrix.one_mulVec]⟩⟩
      intro β γ h
      simp only [Option.some.injEq] at h
      rw [← h, Matrix.one_mulVec]
  | unquad quads lins t =>
    by_cases hd : (∀ p ∈ quads, p.1 ≠ p.2 ∧ p.1 ≠ t ∧ p.2 ≠ t) ∧ t ∉ lins
    · simp only [compile, dite_eq_left hd, run, rawRun, ite_eq_left hd]
      have hmain : ∀ β,
          ((sqrtHalf • ((QRegister.singleton t).basisOutcomeProjector 0 +
            (fixupQuad quads lins t).eval.1 * (QRegister.singleton t).basisOutcomeProjector 1)) *
            (Circuit.H t).eval.1).mulVec (ket β) =
          optKet (if β t = (quads.map (fun p ↦ β p.1 * β p.2)).sum + (lins.map β).sum then
            some (update β t 0) else none) := by
        intro β
        have hH : (Circuit.H t).eval.1.mulVec (ket β) =
            sqrtHalf • (ket (update β t 0) + bitSign (β t) • ket (update β t 1)) := ket_H t β
        have hqmap : quads.map (fun p ↦ (update β t 1) p.1 * (update β t 1) p.2) =
            quads.map (fun p ↦ β p.1 * β p.2) :=
          List.map_congr_left fun p hp ↦ by
            rw [update_of_ne (hd.1 p hp).2.1, update_of_ne (hd.1 p hp).2.2]
        have hlmap : lins.map (update β t 1) = lins.map β :=
          List.map_congr_left fun c hc ↦ update_of_ne (fun eq : c = t ↦ hd.2 (eq ▸ hc)) _ _
        have hF : (fixupQuad quads lins t).eval.1.mulVec (ket (update β t 1)) =
            bitSign ((quads.map (fun p ↦ β p.1 * β p.2)).sum + (lins.map β).sum) •
              ket (update β t 0) := by
          rw [fixupQuad_mulVec_ket _ _ _ (fun p hp ↦ (hd.1 p hp).1), hqmap, hlmap,
            update_self, update_idem, one_add_one_zmod2]
        simp only [← Matrix.mulVec_mulVec, hH, Matrix.mulVec_smul, Matrix.smul_mulVec,
          Matrix.add_mulVec, Matrix.mulVec_add, ket_projector_zero, ket_projector_one, update_self,
          hF, ↓reduceIte, one_ne_zero, zero_ne_one, Matrix.mulVec_zero, add_zero, zero_add]
        rw [unand_scalar]
        split_ifs <;> rfl
      refine ⟨_, (lowerKraus_circuit (Circuit.H t)).qSeq
        (lowerKraus_measure_singleton_qIf v t (lowerKraus_circuit (fixupQuad quads lins t))),
        ?_, fun β ↦ ⟨1, by rw [one_smul, hmain]⟩⟩
      intro β γ h
      rw [hmain, h, optKet]
    · simp only [compile, dite_eq_right hd, run, rawRun, ite_eq_right hd, optKet]
      refine ⟨1, lowerKraus_skip, ?_, fun β ↦ ⟨1, by rw [one_smul, Matrix.one_mulVec]⟩⟩
      intro β γ h
      simp only [Option.some.injEq] at h
      rw [← h, Matrix.one_mulVec]

end Step

/-- Run a list of steps from left to right. -/
def runList : List (Step n) → BitAssignment n → Option (BitAssignment n)
  | [], β => some β
  | s :: ss, β => (s.run β).bind (runList ss)

/-- Underlying support run of a list of steps. -/
def rawRunList : List (Step n) → BitAssignment n → Option (BitAssignment n)
  | [], β => some β
  | s :: ss, β => (s.rawRun β).bind (rawRunList ss)

/-- Compile a list of steps to a sequence of dynamic circuits. -/
def compileList (v : Var) : List (Step n) → DynamicCircuit Var n
  | [] => .identity
  | s :: ss => .seq (s.compile v) (compileList v ss)

@[simp] theorem runList_nil (β : BitAssignment n) : runList [] β = some β := rfl

@[simp] theorem runList_cons (s : Step n) (ss : List (Step n)) (β : BitAssignment n) :
    runList (s :: ss) β = (s.run β).bind (runList ss) := rfl

theorem runList_append (ss ts : List (Step n)) (β : BitAssignment n) :
    runList (ss ++ ts) β = (runList ss β).bind (runList ts) := by
  induction ss generalizing β with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.cons_append, runList_cons, ih]
    cases s.run β <;> rfl

theorem rawRunList_of_runList {ss : List (Step n)} {β γ : BitAssignment n}
    (h : runList ss β = some γ) : rawRunList ss β = some γ := by
  induction ss generalizing β with
  | nil => exact h
  | cons s ss ih =>
    simp only [runList_cons, Option.bind_eq_some_iff] at h
    obtain ⟨δ, hδ, hγ⟩ := h
    simp only [rawRunList, Step.rawRun_of_run hδ, Option.bind_some]
    exact ih hγ

theorem rawRunList_injective {ss : List (Step n)} {β β' γ : BitAssignment n}
    (h : rawRunList ss β = some γ) (h' : rawRunList ss β' = some γ) : β = β' := by
  induction ss generalizing β β' with
  | nil => exact (Option.some.inj h).trans (Option.some.inj h').symm
  | cons s ss ih =>
    simp only [rawRunList, Option.bind_eq_some_iff] at h h'
    obtain ⟨δ, hδ, hγ⟩ := h
    obtain ⟨δ', hδ', hγ'⟩ := h'
    exact Step.rawRun_injective hδ ((ih hγ hγ') ▸ hδ')

theorem exists_lowerKraus_compileList [DecidableEq Var] [NeZero (2 ^ n)]
    (v : Var) (ss : List (Step n)) :
    ∃ R, LowerKraus (compileList v ss).compile R ∧
      (∀ β γ, runList ss β = some γ → R.mulVec (ket β) = ket γ) ∧
      (∀ β, ∃ z : ℂ, R.mulVec (ket β) = z • optKet (rawRunList ss β)) := by
  induction ss with
  | nil =>
    refine ⟨1, lowerKraus_skip, ?_,
      fun β ↦ ⟨1, by rw [one_smul, rawRunList, optKet, Matrix.one_mulVec]⟩⟩
    intro β γ h
    simp only [runList_nil, Option.some.injEq] at h
    rw [← h, Matrix.one_mulVec]
  | cons s ss ih =>
    obtain ⟨R₁, hK₁, hR₁, hRaw₁⟩ := s.exists_lowerKraus v
    obtain ⟨R₂, hK₂, hR₂, hRaw₂⟩ := ih
    refine ⟨R₂ * R₁, hK₁.qSeq hK₂, ?_, ?_⟩
    · intro β γ h
      simp only [runList_cons, Option.bind_eq_some_iff] at h
      obtain ⟨δ, hδ, hγ⟩ := h
      rw [← Matrix.mulVec_mulVec, hR₁ β δ hδ, hR₂ δ γ hγ]
    · intro β
      obtain ⟨z₁, hz₁⟩ := hRaw₁ β
      rw [← Matrix.mulVec_mulVec, hz₁, Matrix.mulVec_smul]
      rcases hraw : s.rawRun β with _ | δ
      · exact ⟨0, by simp [rawRunList, hraw, optKet]⟩
      · obtain ⟨z₂, hz₂⟩ := hRaw₂ δ
        refine ⟨z₁ * z₂, ?_⟩
        simp only [rawRunList, hraw, Option.bind_some, optKet, hz₂, smul_smul]

theorem count_T_compileList (v : Var) (ss : List (Step n)) :
    (compileList v ss).count PrimitiveGate.T ≤ 4 * (ss.map Step.andCount).sum := by
  induction ss with
  | nil => simp [compileList]
  | cons s ss ih =>
    simp only [compileList, DynamicCircuit.count, List.map_cons, List.sum_cons, Nat.mul_add]
    exact Nat.add_le_add (s.count_T_compile v) ih

theorem count_TOFF_compileList (v : Var) (ss : List (Step n)) :
    (compileList v ss).count PrimitiveGate.TOFF = 0 := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [compileList, ih, s.count_TOFF_compile v]

/-- A step list that maps every clean-ancilla basis state by the basis permutation `σ` of the
target register realizes `permutationUnitary σ` as a clean subroutine. -/
theorem realizesCleanSubroutine_compileList [DecidableEq Var] [NeZero (2 ^ n)]
    {k m : ℕ} (v : Var) (ss : List (Step n)) (rTarget : QRegister k n) (rAnc : QRegister m n)
    (hdisj : rTarget.DisjointWires rAnc) (σ : Equiv.Perm (Fin (2 ^ k)))
    (hrun : ∀ β, localIdx rAnc β = 0 →
      runList ss β = some (writeReg β rTarget (basisBits k (σ (localIdx rTarget β))))) :
    RealizesCleanSubroutine rTarget rAnc hdisj (permutationUnitary σ)
      (compileList v ss).compile := by
  obtain ⟨R, hK, hR, hRaw⟩ := exists_lowerKraus_compileList v ss
  refine realizesCleanSubroutine_of_lowerKraus rTarget rAnc hdisj _ hK
    (matrix_ext_ket fun β ↦ ?_)
  have hE : ∀ γ, (rTarget.embedUnitary (permutationUnitary σ)).1.mulVec (ket γ) =
      ket (writeReg γ rTarget (basisBits k (σ (localIdx rTarget γ)))) := fun γ ↦ by
    have h := embedMatrix_permMatrix_mulVec_ket rTarget σ⁻¹ γ
    rw [Equiv.Perm.inv_def, Equiv.symm_symm] at h
    rw [QRegister.embedUnitary_val]
    exact h
  have hanc : ∀ γ δ, localIdx rAnc (writeReg γ rTarget δ) = localIdx rAnc γ :=
    fun γ δ ↦ localIdx_writeReg_of_disjoint γ rTarget rAnc hdisj δ
  simp only [← Matrix.mulVec_mulVec, basisOutcomeProjector_mulVec_ket]
  by_cases hβ : localIdx rAnc β = 0
  · rw [hR β _ (hrun β hβ), ite_eq_left hβ, hE, basisOutcomeProjector_mulVec_ket, hanc,
      ite_eq_left hβ]
  · rw [ite_eq_right hβ, Matrix.mulVec_zero, Matrix.mulVec_zero]
    obtain ⟨z, hz⟩ := hRaw β
    rw [hz, Matrix.mulVec_smul]
    rcases hγ : rawRunList ss β with _ | γ
    · simp [optKet]
    · rw [optKet, basisOutcomeProjector_mulVec_ket, ite_eq_right, smul_zero]
      intro hγ0
      have h0 :
          localIdx rAnc (writeReg γ rTarget (basisBits k (σ.symm (localIdx rTarget γ)))) = 0 := by
        rw [hanc]
        exact hγ0
      have hpre := rawRunList_of_runList (hrun _ h0)
      simp only [localIdx_writeReg, basisBitsEquiv_symm_basisBits, Equiv.apply_symm_apply,
        writeReg_writeReg, writeReg_self] at hpre
      exact hβ (rawRunList_injective hγ hpre ▸ h0)

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


end TableLookupSteps

end QuantumComputation.Specs

/-! BEGIN GOOGLE-DERIVED (EqualTableAdd.lean) -/

namespace QuantumComputation.Specs

namespace TableLookupSteps

open Operator Matrix QProg Function Step
open scoped Matrix ComplexOrder MatrixOrder

variable {n : ℕ}

namespace Step


def Avoids : Step n → Wire n → Prop
  | x q, w => q ≠ w
  | cnot c t, w => c ≠ w ∧ t ≠ w
  | and4t c₁ c₂ t, w => c₁ ≠ w ∧ c₂ ≠ w ∧ t ≠ w
  | rccx0 c₁ c₂ t, w => c₁ ≠ w ∧ c₂ ≠ w ∧ t ≠ w
  | rccx1 c₁ c₂ t, w => c₁ ≠ w ∧ c₂ ≠ w ∧ t ≠ w
  | unand c₁ c₂ t, w => c₁ ≠ w ∧ c₂ ≠ w ∧ t ≠ w
  | unxorList sources t, w => (∀ c ∈ sources, c ≠ w) ∧ t ≠ w
  | unquad quads lins t, w =>
      (∀ p ∈ quads, p.1 ≠ w ∧ p.2 ≠ w) ∧ (∀ c ∈ lins, c ≠ w) ∧ t ≠ w

theorem avoids_inv {s : Step n} {w : Wire n} (h : s.Avoids w) : s.inv.Avoids w := by
  cases s <;> exact h

theorem run_writeReg_of_avoids {k : ℕ} (s : Step n) (r : QRegister k n)
    (h : ∀ i, s.Avoids (r i)) (β : BitAssignment n) (γ : BitAssignment k) :
    s.run (writeReg β r γ) = (s.run β).map (writeReg · r γ) := by
  have hn : ∀ w, (∀ i, w ≠ r i) → w ∉ Set.range r.wires := fun w hw ⟨i, hi⟩ ↦ hw i hi.symm
  cases s with
  | x q =>
    have hq := hn q (fun i ↦ h i)
    simp only [run, Option.map_some, writeReg_apply_of_not_mem _ _ _ _ hq,
      writeReg_update_of_not_mem _ _ _ hq]
  | cnot c t =>
    have hc := hn c (fun i ↦ (h i).1)
    have ht := hn t (fun i ↦ (h i).2)
    simp only [run]
    split_ifs <;> simp only [Option.map_some, writeReg_apply_of_not_mem _ _ _ _ hc,
      writeReg_apply_of_not_mem _ _ _ _ ht, writeReg_update_of_not_mem _ _ _ ht]
  | and4t c₁ c₂ t =>
    have h₁ := hn c₁ (fun i ↦ (h i).1)
    have h₂ := hn c₂ (fun i ↦ (h i).2.1)
    have ht := hn t (fun i ↦ (h i).2.2)
    simp only [run, writeReg_apply_of_not_mem _ _ _ _ h₁, writeReg_apply_of_not_mem _ _ _ _ h₂,
      writeReg_apply_of_not_mem _ _ _ _ ht]
    split_ifs <;> simp only [Option.map_some, Option.map_none,
      writeReg_update_of_not_mem _ _ _ ht]
  | rccx0 c₁ c₂ t =>
    have h₁ := hn c₁ (fun i ↦ (h i).1)
    have h₂ := hn c₂ (fun i ↦ (h i).2.1)
    have ht := hn t (fun i ↦ (h i).2.2)
    simp only [run, writeReg_apply_of_not_mem _ _ _ _ h₁, writeReg_apply_of_not_mem _ _ _ _ h₂,
      writeReg_apply_of_not_mem _ _ _ _ ht]
    split_ifs <;> simp only [Option.map_some, Option.map_none,
      writeReg_update_of_not_mem _ _ _ ht]
  | rccx1 c₁ c₂ t =>
    have h₁ := hn c₁ (fun i ↦ (h i).1)
    have h₂ := hn c₂ (fun i ↦ (h i).2.1)
    have ht := hn t (fun i ↦ (h i).2.2)
    simp only [run, writeReg_apply_of_not_mem _ _ _ _ h₁, writeReg_apply_of_not_mem _ _ _ _ h₂,
      writeReg_apply_of_not_mem _ _ _ _ ht]
    split_ifs <;> simp only [Option.map_some, Option.map_none,
      writeReg_update_of_not_mem _ _ _ ht]
  | unand c₁ c₂ t =>
    have h₁ := hn c₁ (fun i ↦ (h i).1)
    have h₂ := hn c₂ (fun i ↦ (h i).2.1)
    have ht := hn t (fun i ↦ (h i).2.2)
    simp only [run, writeReg_apply_of_not_mem _ _ _ _ h₁, writeReg_apply_of_not_mem _ _ _ _ h₂,
      writeReg_apply_of_not_mem _ _ _ _ ht]
    split_ifs <;> simp only [Option.map_some, Option.map_none,
      writeReg_update_of_not_mem _ _ _ ht]
  | unxorList sources t =>
    have ht := hn t (fun i ↦ (h i).2)
    have hmap : sources.map (writeReg β r γ) = sources.map β :=
      List.map_congr_left fun c hc ↦
        writeReg_apply_of_not_mem _ _ _ _ (hn c (fun i ↦ (h i).1 c hc))
    simp only [run, writeReg_apply_of_not_mem _ _ _ _ ht, hmap]
    split_ifs <;> simp only [Option.map_some, Option.map_none,
      writeReg_update_of_not_mem _ _ _ ht]
  | unquad quads lins t =>
    have ht := hn t (fun i ↦ (h i).2.2)
    have hqmap : quads.map (fun p ↦ (writeReg β r γ) p.1 * (writeReg β r γ) p.2) =
        quads.map (fun p ↦ β p.1 * β p.2) :=
      List.map_congr_left fun p hp ↦ by
        rw [writeReg_apply_of_not_mem _ _ _ _ (hn p.1 (fun i ↦ ((h i).1 p hp).1)),
            writeReg_apply_of_not_mem _ _ _ _ (hn p.2 (fun i ↦ ((h i).1 p hp).2))]
    have hlmap : lins.map (writeReg β r γ) = lins.map β :=
      List.map_congr_left fun c hc ↦
        writeReg_apply_of_not_mem _ _ _ _ (hn c (fun i ↦ (h i).2.1 c hc))
    simp only [run, writeReg_apply_of_not_mem _ _ _ _ ht, hqmap, hlmap]
    split_ifs <;> simp only [Option.map_some, Option.map_none,
      writeReg_update_of_not_mem _ _ _ ht]

theorem run_inv {s : Step n} (hno : s.NoUnxor) {β γ : BitAssignment n} (hs : s.run β = some γ) :
    s.inv.run γ = some β := by
  have hb : ∀ a b : ZMod 2, a + b + b = a := fun a b ↦ by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  cases s with
  | x q =>
    simp only [run, inv, Option.some.injEq] at hs ⊢
    rw [← hs, update_self, update_idem, hb, update_eq_self]
  | cnot c t =>
    simp only [run, inv] at hs ⊢
    split_ifs at hs with hct <;> simp only [Option.some.injEq] at hs <;> rw [← hs]
    · rw [ite_eq_left hct, update_self, update_of_ne hct, update_idem, hb, update_eq_self]
    · rw [ite_eq_right hct]
  | and4t c₁ c₂ t =>
    simp only [run, inv] at hs ⊢
    split_ifs at hs with hct ht0 <;> simp only [Option.some.injEq] at hs <;> rw [← hs]
    · rw [ite_eq_left hct, update_self, update_of_ne hct.2.1, update_of_ne hct.2.2, ite_eq_left rfl,
        Option.some.injEq, update_idem, ← ht0, update_eq_self]
    · rw [ite_eq_right hct]
  | unand c₁ c₂ t =>
    simp only [run, inv] at hs ⊢
    split_ifs at hs with hct ht <;> simp only [Option.some.injEq] at hs <;> rw [← hs]
    · rw [ite_eq_left hct, update_self, ite_eq_left rfl, update_of_ne hct.2.1, update_of_ne hct.2.2,
        Option.some.injEq, update_idem, ← ht, update_eq_self]
    · rw [ite_eq_right hct]
  | rccx0 _ _ _ => exact hno.elim
  | rccx1 _ _ _ => exact hno.elim
  | unxorList _ _ => exact hno.elim
  | unquad _ _ _ => exact hno.elim
end Step

theorem runList_writeReg_of_avoids {k : ℕ} (ss : List (Step n)) (r : QRegister k n)
    (h : ∀ s ∈ ss, ∀ i, s.Avoids (r i)) (β : BitAssignment n) (γ : BitAssignment k) :
    runList ss (writeReg β r γ) = (runList ss β).map (writeReg · r γ) := by
  induction ss generalizing β with
  | nil => rfl
  | cons s ss ih =>
    rw [runList_cons, runList_cons, Step.run_writeReg_of_avoids s r (h s List.mem_cons_self)]
    rcases s.run β with _ | δ
    · rfl
    · exact ih (fun s hs ↦ h s (List.mem_cons_of_mem _ hs)) δ

theorem runList_inv {ss : List (Step n)} (hno : ∀ s ∈ ss, s.NoUnxor) {β γ : BitAssignment n}
    (hs : runList ss β = some γ) :
    runList (ss.reverse.map Step.inv) γ = some β := by
  induction ss generalizing β with
  | nil => exact (Option.some.inj hs).symm ▸ rfl
  | cons s ss ih =>
    rw [runList_cons, Option.bind_eq_some_iff] at hs
    obtain ⟨δ, hδ, hγ⟩ := hs
    rw [List.reverse_cons, List.map_append, List.map_singleton, runList_append,
      ih (fun s hs ↦ hno s (List.mem_cons_of_mem _ hs)) hγ,
      Option.bind_some, runList_cons, Step.run_inv (hno s List.mem_cons_self) hδ,
      Option.bind_some, runList_nil]

open Step

variable {n : ℕ}

theorem add_add_self_zmod2 (x y : ZMod 2) : x + y + y = x := by
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem two_eq_zero_zmod2 : (2 : ZMod 2) = 0 := rfl

theorem maj_val (a b c : ZMod 2) : ((a + c) * (b + c) + c).val = (a.val + b.val + c.val) / 2 := by
  revert a b c
  decide

theorem bit_zero_mod_two_pow (x K : ℕ) :
    ((x % 2 ^ (K + 1) / 2 ^ ((0 : Fin (K + 1)) : ℕ) % 2 : ℕ) : ZMod 2) = x := by
  rw [Fin.val_zero, pow_zero, Nat.div_one, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 K.succ_ne_zero),
    ZMod.natCast_mod]

theorem bit_succ_mod_two_pow (x K : ℕ) (i : Fin (K + 1)) :
    x % 2 ^ (K + 2) / 2 ^ (i.succ : ℕ) % 2 = x / 2 % 2 ^ (K + 1) / 2 ^ (i : ℕ) % 2 := by
  rw [Fin.val_succ, pow_succ' 2 (i : ℕ), ← Nat.div_div_eq_div_mul, pow_succ' 2 (K + 1),
    Nat.mod_mul_right_div_self]

/-- Ripple-carry core on `k + 1` bits using 4-`T` `and4t` + 0-`T` `unand`. -/
def rippleSteps : (k : ℕ) → QRegister (k + 1) n → QRegister (k + 1) n → Wire n →
    QRegister k n → List (Step n)
  | 0, rA, rB, ci, _ => [cnot (rA 0) (rB 0), cnot ci (rB 0)]
  | k + 1, rA, rB, ci, rC =>
      [cnot ci (rA 0), cnot ci (rB 0), and4t (rA 0) (rB 0) (rC 0), cnot ci (rC 0)] ++
        rippleSteps k (regTail rA) (regTail rB) (rC 0) (regTail rC) ++
        [cnot ci (rC 0), unand (rA 0) (rB 0) (rC 0), cnot ci (rA 0), cnot (rA 0) (rB 0)]

theorem runList_rippleSteps (k : ℕ) (rA rB : QRegister (k + 1) n) (ci : Wire n)
    (rC : QRegister k n) (hAB : rA.DisjointWires rB) (hAC : rA.DisjointWires rC)
    (hBC : rB.DisjointWires rC) (hA : ci ∉ Set.range rA.wires) (hB : ci ∉ Set.range rB.wires)
    (hC : ci ∉ Set.range rC.wires) (β : BitAssignment n) (hclean : ∀ i, β (rC i) = 0) :
    runList (rippleSteps k rA rB ci rC) β = some (writeReg β rB (basisBits (k + 1)
      ⟨((localIdx rA β : ℕ) + (localIdx rB β : ℕ) + (β ci).val) % 2 ^ (k + 1),
        Nat.mod_lt _ (by positivity)⟩)) := by
  induction k generalizing ci β with
  | zero =>
    have hab : rA 0 ≠ rB 0 := hAB.ne 0 0
    have hib : ci ≠ rB 0 := fun h ↦ hB ⟨0, h.symm⟩
    simp only [rippleSteps, runList_cons, Step.run, ite_eq_left hab, ite_eq_left hib,
      Option.bind_some, runList_nil, update_self, update_idem, update_of_ne hib]
    rw [writeReg_eq_update _ _ _ 0 (fun i hi ↦ absurd (Fin.fin_one_eq_zero i) hi),
      basisBits_mk_apply, bit_zero_mod_two_pow, localIdx_val_succ, localIdx_val_succ,
      Option.some.injEq]
    congr 1
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val,
      two_eq_zero_zmod2, zero_mul, add_zero]
    ring
  | succ k ih =>
    have hab : rA 0 ≠ rB 0 := hAB.ne 0 0
    have hac : rA 0 ≠ rC 0 := hAC.ne 0 0
    have hbc : rB 0 ≠ rC 0 := hBC.ne 0 0
    have hia : ci ≠ rA 0 := fun h ↦ hA ⟨0, h.symm⟩
    have hib : ci ≠ rB 0 := fun h ↦ hB ⟨0, h.symm⟩
    have hic : ci ≠ rC 0 := fun h ↦ hC ⟨0, h.symm⟩
    have hcA : rC 0 ∉ Set.range rA.wires := fun ⟨i, h⟩ ↦ hAC.ne i 0 h
    have hcB : rC 0 ∉ Set.range rB.wires := fun ⟨i, h⟩ ↦ hBC.ne i 0 h
    have hbA : rB 0 ∉ Set.range rA.wires := fun ⟨i, h⟩ ↦ hAB.ne i 0 h
    have haB' : rA 0 ∉ Set.range (regTail rB).wires := not_mem_regTail (not_mem_of_disjoint hAB 0)
    have hbB' : rB 0 ∉ Set.range (regTail rB).wires := zero_not_mem_regTail rB
    have hcB' : rC 0 ∉ Set.range (regTail rB).wires := not_mem_regTail hcB
    have hiB' : ci ∉ Set.range (regTail rB).wires := not_mem_regTail hB
    obtain ⟨β1, hβ1⟩ : ∃ β1, β1 = update (update (update β (rA 0) (β (rA 0) + β ci)) (rB 0)
        (β (rB 0) + β ci)) (rC 0) ((β (rA 0) + β ci) * (β (rB 0) + β ci) + β ci) := ⟨_, rfl⟩
    have hβ1o : ∀ w, w ≠ rA 0 → w ≠ rB 0 → w ≠ rC 0 → β1 w = β w := fun w h₁ h₂ h₃ ↦ by
      rw [hβ1, update_of_ne h₃, update_of_ne h₂, update_of_ne h₁]
    have hβ1i : β1 ci = β ci := hβ1o ci hia hib hic
    have hfwd : runList [cnot ci (rA 0), cnot ci (rB 0), and4t (rA 0) (rB 0) (rC 0),
        cnot ci (rC 0)] β = some β1 := by
      rw [hβ1]
      simp [Step.run, hab, hac, hbc, hia, hib, hic, hab.symm, hac.symm, hbc.symm, hclean 0]
    have hcl1 : ∀ i, β1 (regTail rC i) = 0 := fun i ↦ by
      rw [hβ1o _ (fun h ↦ hAC.ne 0 i.succ (h.symm.trans (regTail_apply rC i)))
        (fun h ↦ hBC.ne 0 i.succ (h.symm.trans (regTail_apply rC i))) (regTail_ne_zero rC i),
        regTail_apply]
      exact hclean i.succ
    have hidx : ∀ r : QRegister (k + 1) n, rA 0 ∉ Set.range r.wires → rB 0 ∉ Set.range r.wires →
        rC 0 ∉ Set.range r.wires → localIdx r β1 = localIdx r β := fun r h₁ h₂ h₃ ↦ by
      rw [hβ1, localIdx_update_of_not_mem _ _ h₃, localIdx_update_of_not_mem _ _ h₂,
        localIdx_update_of_not_mem _ _ h₁]
    have hcore := ih (regTail rA) (regTail rB) (rC 0) (regTail rC)
      ((hAB.compose_left _).compose_right _) ((hAC.compose_left _).compose_right _)
      ((hBC.compose_left _).compose_right _) (not_mem_regTail hcA) hcB'
      (zero_not_mem_regTail rC) β1 hcl1
    rw [hidx _ (zero_not_mem_regTail rA) (not_mem_regTail hbA) (not_mem_regTail hcA),
      hidx _ haB' hbB' hcB'] at hcore
    have hβ1a : β1 (rA 0) = β (rA 0) + β ci := by
      rw [hβ1, update_of_ne hac, update_of_ne hab, update_self]
    have hβ1b : β1 (rB 0) = β (rB 0) + β ci := by rw [hβ1, update_of_ne hbc, update_self]
    have hβ1c : β1 (rC 0) = (β (rA 0) + β ci) * (β (rB 0) + β ci) + β ci := by
      rw [hβ1, update_self]
    have hcond : β1 (rC 0) + β ci = β1 (rA 0) * β1 (rB 0) := by
      rw [hβ1a, hβ1b, hβ1c, add_add_self_zmod2]
    have hT : ((localIdx rA β : ℕ) + (localIdx rB β : ℕ) + (β ci).val) / 2 =
        (localIdx (regTail rA) β : ℕ) + (localIdx (regTail rB) β : ℕ) + (β1 (rC 0)).val := by
      rw [localIdx_val_succ rA β, localIdx_val_succ rB β, hβ1c, maj_val]
      omega
    rw [rippleSteps, runList_append, runList_append, hfwd, Option.bind_some, hcore,
      Option.bind_some]
    simp only [runList_cons, runList_nil, Step.run, ite_eq_left hic, ite_eq_left hia,
      ite_eq_left hab,
      ite_eq_left (show rA 0 ≠ rB 0 ∧ rA 0 ≠ rC 0 ∧ rB 0 ≠ rC 0 from ⟨hab, hac, hbc⟩),
      update_self, update_of_ne hic, update_of_ne hac, update_of_ne hbc,
      writeReg_apply_of_not_mem _ _ _ _ hcB', writeReg_apply_of_not_mem _ _ _ _ hiB',
      writeReg_apply_of_not_mem _ _ _ _ haB', writeReg_apply_of_not_mem _ _ _ _ hbB', hβ1i,
      ite_eq_left hcond, Option.bind_some, Option.some.injEq]
    rw [writeReg_succ β rB]
    funext w
    by_cases hw0 : w = rB 0
    · subst hw0
      rw [update_self, update_self, update_of_ne hab.symm, update_of_ne hbc, update_of_ne hbc,
        writeReg_apply_of_not_mem _ _ _ _ hbB', basisBits_mk_apply, bit_zero_mod_two_pow,
        localIdx_val_succ rA β, localIdx_val_succ rB β, hβ1a, hβ1b]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val,
        two_eq_zero_zmod2, zero_mul, add_zero, add_add_self_zmod2]
      ring
    · rw [update_of_ne hw0, update_of_ne hw0]
      by_cases hwa : w = rA 0
      · subst hwa
        rw [update_self, hβ1a, add_add_self_zmod2, writeReg_apply_of_not_mem _ _ _ _ haB']
      · rw [update_of_ne hwa]
        by_cases hwc : w = rC 0
        · subst hwc
          rw [update_self, writeReg_apply_of_not_mem _ _ _ _ hcB', hclean 0]
        · rw [update_of_ne hwc, update_of_ne hwc]
          by_cases hwB : w ∈ Set.range (regTail rB).wires
          · obtain ⟨i, rfl⟩ := hwB
            rw [writeReg_apply_reg, writeReg_apply_reg, basisBits_mk_apply, basisBits_mk_apply,
              bit_succ_mod_two_pow, hT]
          · rw [writeReg_apply_of_not_mem _ _ _ _ hwB, writeReg_apply_of_not_mem _ _ _ _ hwB,
              hβ1o w hwa hw0 hwc]

variable {n : ℕ}

/-- Value of an optional control wire, `1` when there is no control. -/
def ctrlVal : Option (Wire n) → BitAssignment n → ZMod 2
  | none, _ => 1
  | some c, β => β c

/-- Flip of the wire `t`, controlled by the optional control wire. -/
def ctrlFlip : Option (Wire n) → Wire n → Step n
  | none, t => x t
  | some c, t => cnot c t

/-- The optional control wire `c` is not the wire `w`. -/
def CtrlNe (c : Option (Wire n)) (w : Wire n) : Prop := ∀ c₀, c = some c₀ → c₀ ≠ w

theorem ctrlVal_update {c : Option (Wire n)} {w : Wire n} (h : CtrlNe c w) (β : BitAssignment n)
    (a : ZMod 2) : ctrlVal c (update β w a) = ctrlVal c β := by
  cases c with
  | none => rfl
  | some c₀ => exact update_of_ne (h c₀ rfl) _ _

theorem ctrlVal_writeReg {k : ℕ} {c : Option (Wire n)} {r : QRegister k n}
    (h : ∀ i, CtrlNe c (r i)) (β : BitAssignment n) (γ : BitAssignment k) :
    ctrlVal c (writeReg β r γ) = ctrlVal c β := by
  cases c with
  | none => rfl
  | some c₀ => exact writeReg_apply_of_not_mem _ _ _ _ fun ⟨i, hi⟩ ↦ h i c₀ rfl hi.symm

theorem run_ctrlFlip {c : Option (Wire n)} {t : Wire n} (h : CtrlNe c t) (β : BitAssignment n) :
    (ctrlFlip c t).run β = some (update β t (β t + ctrlVal c β)) := by
  cases c with
  | none => rfl
  | some c₀ => exact ite_eq_left (h c₀ rfl)

/-- XOR of the constant `d` into the register `rY`, controlled by `c`. -/
def xorSteps (c : Option (Wire n)) : (w : ℕ) → QRegister w n → BitAssignment w → List (Step n)
  | 0, _, _ => []
  | w + 1, rY, d => (if d 0 = 1 then [ctrlFlip c (rY 0)] else []) ++
      xorSteps c w (regTail rY) (fun i ↦ d i.succ)

theorem runList_xorSteps (c : Option (Wire n)) (w : ℕ) (rY : QRegister w n)
    (d : BitAssignment w) (hc : ∀ i, CtrlNe c (rY i)) (β : BitAssignment n) :
    runList (xorSteps c w rY d) β =
      some (writeReg β rY (fun i ↦ β (rY i) + ctrlVal c β * d i)) := by
  induction w generalizing β with
  | zero =>
    rw [xorSteps, runList_nil, show (fun i : Fin 0 ↦ β (rY i) + ctrlVal c β * d i) =
      fun i ↦ β (rY i) from funext fun i ↦ i.elim0, writeReg_self]
  | succ w ih =>
    have hhead : runList (if d 0 = 1 then [ctrlFlip c (rY 0)] else []) β =
        some (update β (rY 0) (β (rY 0) + ctrlVal c β * d 0)) := by
      split_ifs with hd
      · rw [runList_cons, run_ctrlFlip (hc 0), Option.bind_some, runList_nil, hd, mul_one]
      · rw [(bit_cases (d 0)).resolve_right hd, mul_zero, add_zero, update_eq_self, runList_nil]
    rw [xorSteps, runList_append, hhead, Option.bind_some,
      ih (regTail rY) (fun i ↦ d i.succ) (fun i ↦ by rw [regTail_apply]; exact hc i.succ),
      ctrlVal_update (hc 0), writeReg_succ β rY,
      writeReg_update_of_not_mem _ _ _ (zero_not_mem_regTail rY)]
    congr 3
    funext i
    rw [update_of_ne (regTail_ne_zero rY i), regTail_apply]

/-- Steps computing `c ∧ ¬t` into the clean wire `c'` using 4-`T` `and4t`. -/
def andNotSteps : Option (Wire n) → Wire n → Wire n → List (Step n)
  | none, t, c' => [x t, cnot t c', x t]
  | some c, t, c' => [x t, and4t c t c', x t]

/-- Steps uncomputing `c' = c ∧ t` in 0 `T` gates (`unand`). -/
def unAndSteps : Option (Wire n) → Wire n → Wire n → List (Step n)
  | none, t, c' => [cnot t c']
  | some c, t, c' => [unand c t c']

/-- Unary-iteration lookup using `and4t` (`4 T`) and `unand` (`0 T`). -/
def lookupSteps (w : ℕ) (rY : QRegister w n) : (m : ℕ) → Option (Wire n) → QRegister m n →
    QRegister m n → (ℕ → BitAssignment w) → List (Step n)
  | 0, c, _, _, T => xorSteps c w rY (T 0)
  | m + 1, c, rX, rW, T =>
      andNotSteps c (rX 0) (rW 0) ++
      lookupSteps w rY m (some (rW 0)) (regTail rX) (regTail rW) (fun j ↦ T (2 * j)) ++
      [ctrlFlip c (rW 0)] ++
      lookupSteps w rY m (some (rW 0)) (regTail rX) (regTail rW) (fun j ↦ T (2 * j + 1)) ++
      unAndSteps c (rX 0) (rW 0)

theorem CtrlNe.some {a w : Wire n} (h : a ≠ w) : CtrlNe (some a) w :=
  fun _ h' ↦ Option.some.inj h' ▸ h

theorem runList_andNotSteps (c : Option (Wire n)) (t c' : Wire n) (htc : t ≠ c')
    (hct : CtrlNe c t) (hcc : CtrlNe c c') (β : BitAssignment n) (h0 : β c' = 0) :
    runList (andNotSteps c t c') β = some (update β c' (ctrlVal c β * (β t + 1))) := by
  have hb : β t + 1 + 1 = β t := by rw [add_assoc, one_add_one_zmod2, add_zero]
  cases c with
  | none =>
    simp only [andNotSteps, runList_cons, Step.run, ite_eq_left htc, Option.bind_some, runList_nil,
      update_self, update_of_ne htc.symm, update_of_ne htc, h0, zero_add, ctrlVal, one_mul,
      Option.some.injEq]
    rw [update_comm htc, update_idem, hb, update_comm htc.symm, update_eq_self]
  | some c₀ =>
    have h₁ := hct c₀ rfl
    have h₂ := hcc c₀ rfl
    simp only [andNotSteps, runList_cons, Step.run, ite_eq_left (show c₀ ≠ t ∧ c₀ ≠ c' ∧ t ≠ c' from
      ⟨h₁, h₂, htc⟩), Option.bind_some, runList_nil, update_self, update_of_ne htc.symm,
      update_of_ne htc, update_of_ne h₁, h0, ↓reduceIte, ctrlVal, Option.some.injEq]
    rw [update_comm htc, update_idem, hb, update_comm htc.symm, update_eq_self, mul_comm]

theorem runList_unAndSteps (c : Option (Wire n)) (t c' : Wire n) (htc : t ≠ c')
    (hct : CtrlNe c t) (hcc : CtrlNe c c') (β : BitAssignment n)
    (h : β c' = ctrlVal c β * β t) :
    runList (unAndSteps c t c') β = some (update β c' 0) := by
  cases c with
  | none =>
    simp only [unAndSteps, runList_cons, Step.run, ite_eq_left htc, Option.bind_some,
      runList_nil, h, ctrlVal, one_mul, CharTwo.add_self_eq_zero]
  | some c₀ =>
    simp only [ctrlVal] at h
    simp only [unAndSteps, runList_cons, Step.run, ite_eq_left (show c₀ ≠ t ∧ c₀ ≠ c' ∧ t ≠ c' from
      ⟨hct c₀ rfl, hcc c₀ rfl, htc⟩), ite_eq_left h, Option.bind_some, runList_nil]

theorem runList_lookupSteps (w : ℕ) (rY : QRegister w n) (m : ℕ) (c : Option (Wire n))
    (rX rW : QRegister m n) (T : ℕ → BitAssignment w) (hXW : rX.DisjointWires rW)
    (hXY : rX.DisjointWires rY) (hWY : rW.DisjointWires rY) (hcX : ∀ i, CtrlNe c (rX i))
    (hcW : ∀ i, CtrlNe c (rW i)) (hcY : ∀ i, CtrlNe c (rY i)) (β : BitAssignment n)
    (hclean : ∀ i, β (rW i) = 0) :
    runList (lookupSteps w rY m c rX rW T) β =
      some (writeReg β rY (fun i ↦ β (rY i) + ctrlVal c β * T (localIdx rX β) i)) := by
  induction m generalizing c T β with
  | zero =>
    have h0 : (localIdx rX β : ℕ) = 0 := Nat.lt_one_iff.mp (by simp)
    rw [lookupSteps, runList_xorSteps c w rY _ hcY, h0]
  | succ m ih =>
    have htc : rX 0 ≠ rW 0 := hXW.ne 0 0
    have hcY' : rW 0 ∉ Set.range rY.wires := not_mem_of_disjoint hWY 0
    have htY : rX 0 ∉ Set.range rY.wires := not_mem_of_disjoint hXY 0
    have hcX' : rW 0 ∉ Set.range (regTail rX).wires :=
      fun ⟨i, h⟩ ↦ hXW.ne i.succ 0 (by rw [← regTail_apply]; exact h)
    have hXY' : (regTail rX).DisjointWires rY := hXY.compose_left _
    have hWY' : (regTail rW).DisjointWires rY := hWY.compose_left _
    have hstep : ∀ (F : BitAssignment w) (a : ZMod 2) (T' : ℕ → BitAssignment w),
        runList (lookupSteps w rY m (some (rW 0)) (regTail rX) (regTail rW) T')
          (update (writeReg β rY F) (rW 0) a) =
        some (update (writeReg β rY (fun i ↦ F i + a * T' (localIdx (regTail rX) β) i))
          (rW 0) a) := by
      intro F a T'
      rw [ih (some (rW 0)) (regTail rX) (regTail rW) T' ((hXW.compose_left _).compose_right _)
        hXY' hWY' (fun i ↦ CtrlNe.some fun h ↦ hcX' ⟨i, h.symm⟩)
        (fun i ↦ CtrlNe.some (regTail_ne_zero rW i).symm) (fun i ↦ CtrlNe.some (hWY.ne 0 i)) _
        (fun i ↦ by rw [update_of_ne (regTail_ne_zero rW i), writeReg_apply_of_not_mem _ _ _ _
          (not_mem_of_disjoint hWY' i), regTail_apply, hclean]),
        localIdx_update_of_not_mem _ _ hcX',
        localIdx_writeReg_of_disjoint _ _ _ (QRegister.disjoint_comm.mp hXY'),
        writeReg_update_of_not_mem _ _ _ hcY', writeReg_writeReg]
      simp only [ctrlVal, update_self]
      congr 3
      funext i
      rw [update_of_ne (hWY.ne 0 i).symm, writeReg_apply_reg]
    have hβ : update β (rW 0) (ctrlVal c β * (β (rX 0) + 1)) =
        update (writeReg β rY (fun i ↦ β (rY i))) (rW 0) (ctrlVal c β * (β (rX 0) + 1)) := by
      rw [writeReg_self]
    rw [lookupSteps, runList_append, runList_append, runList_append, runList_append,
      runList_andNotSteps c _ _ htc (hcX 0) (hcW 0) β (hclean 0), Option.bind_some, hβ, hstep,
      Option.bind_some, runList_cons, run_ctrlFlip (hcW 0), Option.bind_some, runList_nil,
      Option.bind_some, update_self, ctrlVal_update (hcW 0), ctrlVal_writeReg hcY, update_idem,
      hstep, Option.bind_some, runList_unAndSteps c _ _ htc (hcX 0) (hcW 0), update_idem,
      update_eq_self_iff.mpr (by rw [writeReg_apply_of_not_mem _ _ _ _ hcY', hclean])]
    · congr 2
      funext i
      rw [localIdx_val_succ rX β]
      rcases bit_cases (β (rX 0)) with hb | hb <;> rw [hb]
      · rw [ZMod.val_zero, zero_add, zero_add, mul_one, CharTwo.add_self_eq_zero, zero_mul,
          add_zero]
      · rw [ZMod.val_one, one_add_one_zmod2, mul_zero, zero_mul, add_zero, zero_add, add_comm 1]
    · rw [update_self, ctrlVal_update (hcW 0), ctrlVal_writeReg hcY, update_of_ne htc,
        writeReg_apply_of_not_mem _ _ _ _ htY, mul_add, mul_one, add_assoc,
        CharTwo.add_self_eq_zero, add_zero]

variable {n : ℕ}

/-- Swap of registers `rA` and `rB`, controlled by wire `c`, using clean wire `w_clean`
(`4 T` per bit). -/
def cswapSteps (c w_clean : Wire n) : (w : ℕ) → QRegister w n → QRegister w n → List (Step n)
  | 0, _, _ => []
  | w + 1, rA, rB =>
      [cnot (rB 0) (rA 0), and4t c (rA 0) w_clean, cnot w_clean (rB 0),
       unand c (rA 0) w_clean, cnot (rB 0) (rA 0)] ++
        cswapSteps c w_clean w (regTail rA) (regTail rB)

theorem cswapSteps_avoids (c w_clean : Wire n) (w : ℕ) (rA rB : QRegister w n) (v : Wire n)
    (hc : c ≠ v) (hwc : w_clean ≠ v) (hA : v ∉ Set.range rA.wires) (hB : v ∉ Set.range rB.wires) :
    ∀ s ∈ cswapSteps c w_clean w rA rB, s.Avoids v := by
  induction w with
  | zero => simp [cswapSteps]
  | succ w ih =>
    have ha : rA 0 ≠ v := fun h ↦ hA ⟨0, h⟩
    have hb : rB 0 ≠ v := fun h ↦ hB ⟨0, h⟩
    intro s hs
    simp only [cswapSteps, List.cons_append, List.mem_cons, List.nil_append] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | hs
    · exact ⟨hb, ha⟩
    · exact ⟨hc, ha, hwc⟩
    · exact ⟨hwc, hb⟩
    · exact ⟨hc, ha, hwc⟩
    · exact ⟨hb, ha⟩
    · exact ih _ _ (not_mem_regTail hA) (not_mem_regTail hB) s hs

theorem runList_cswapSteps (c w_clean : Wire n) (w : ℕ) (rA rB : QRegister w n)
    (hAB : rA.DisjointWires rB) (hcA : c ∉ Set.range rA.wires) (hcB : c ∉ Set.range rB.wires)
    (hwc : c ≠ w_clean) (hwA : w_clean ∉ Set.range rA.wires) (hwB : w_clean ∉ Set.range rB.wires)
    (β : BitAssignment n) (hw0 : β w_clean = 0) :
    ∃ β', runList (cswapSteps c w_clean w rA rB) β = some β' ∧
      (∀ v, v ∉ Set.range rA.wires → v ∉ Set.range rB.wires → β' v = β v) ∧
      (∀ i, β' (rA i) = β (rA i) + β c * (β (rA i) + β (rB i))) ∧
      (∀ i, β' (rB i) = β (rB i) + β c * (β (rA i) + β (rB i))) := by
  induction w generalizing β with
  | zero => exact ⟨β, rfl, fun _ _ _ ↦ rfl, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
  | succ w ih =>
    have hab : rA 0 ≠ rB 0 := hAB.ne 0 0
    have hca : c ≠ rA 0 := fun h ↦ hcA ⟨0, h.symm⟩
    have hcb : c ≠ rB 0 := fun h ↦ hcB ⟨0, h.symm⟩
    have haw : rA 0 ≠ w_clean := fun h ↦ hwA ⟨0, h⟩
    have hbw : rB 0 ≠ w_clean := fun h ↦ hwB ⟨0, h⟩
    obtain ⟨β1, hβ1⟩ : ∃ β1, β1 = update (update β (rA 0) (β (rA 0) + β c *
        (β (rA 0) + β (rB 0)))) (rB 0) (β (rB 0) + β c * (β (rA 0) + β (rB 0))) := ⟨_, rfl⟩
    have h3 : runList [cnot (rB 0) (rA 0), and4t c (rA 0) w_clean, cnot w_clean (rB 0),
        unand c (rA 0) w_clean, cnot (rB 0) (rA 0)] β = some β1 := by
      have hb : ∀ a b x : ZMod 2, a + b + (b + x * (a + b)) = a + x * (a + b) := fun a b x ↦ by
        rw [← add_assoc, add_assoc a b b, CharTwo.add_self_eq_zero, add_zero]
      simp only [runList_cons, Step.run, ite_eq_left hab.symm,
        ite_eq_left (show c ≠ rA 0 ∧ c ≠ w_clean ∧ rA 0 ≠ w_clean from ⟨hca, hwc, haw⟩),
        ite_eq_left hbw.symm, Option.bind_some, runList_nil,
        update_of_ne haw.symm, update_of_ne hbw.symm, hw0, ↓reduceIte,
        update_self, update_of_ne hca, update_of_ne hcb, update_of_ne hwc, update_of_ne hab.symm,
        update_of_ne hab, update_of_ne haw, update_of_ne hbw, hβ1, Option.some.injEq]
      funext v
      by_cases hva : v = rA 0
      · subst hva; simp only [update_self, update_of_ne hab, hb]
      · by_cases hvb : v = rB 0
        · subst hvb; simp only [update_of_ne hab.symm, update_self, update_of_ne hbw]
        · by_cases hvw : v = w_clean
          · subst hvw; simp only [update_of_ne haw.symm, update_of_ne hbw.symm, update_self, hw0]
          · simp only [update_of_ne hva, update_of_ne hvb, update_of_ne hvw]
    have hβ1o : ∀ v, v ≠ rA 0 → v ≠ rB 0 → β1 v = β v := fun v h₁ h₂ ↦ by
      rw [hβ1, update_of_ne h₂, update_of_ne h₁]
    obtain ⟨β2, h2, hfr, h2A, h2B⟩ := ih (regTail rA) (regTail rB)
      ((hAB.compose_left _).compose_right _) (not_mem_regTail hcA) (not_mem_regTail hcB)
      (not_mem_regTail hwA) (not_mem_regTail hwB) β1 (by rw [hβ1o w_clean haw.symm hbw.symm, hw0])
    refine ⟨β2, by rw [cswapSteps, runList_append, h3, Option.bind_some, h2],
      fun v hvA hvB ↦ by
        rw [hfr v (not_mem_regTail hvA) (not_mem_regTail hvB),
          hβ1o v (fun h ↦ hvA ⟨0, h.symm⟩) (fun h ↦ hvB ⟨0, h.symm⟩)],
      fun i ↦ ?_, fun i ↦ ?_⟩
    · cases i using Fin.cases with
      | zero =>
        rw [hfr _ (zero_not_mem_regTail rA) (not_mem_regTail (not_mem_of_disjoint hAB 0)),
          hβ1, update_of_ne hab, update_self]
      | succ j =>
        rw [← regTail_apply, h2A, hβ1o _ (regTail_ne_zero rA j)
          (fun h ↦ hAB.ne j.succ 0 (by rw [← regTail_apply]; exact h)),
          hβ1o _ (fun h ↦ hAB.ne 0 j.succ (by rw [← regTail_apply]; exact h.symm))
          (regTail_ne_zero rB j), hβ1o c hca hcb, regTail_apply, regTail_apply]
    · cases i using Fin.cases with
      | zero =>
        rw [hfr _ (fun ⟨j, h⟩ ↦ hAB.ne j.succ 0 (by rw [← regTail_apply]; exact h))
          (zero_not_mem_regTail rB), hβ1, update_self]
      | succ j =>
        rw [← regTail_apply, h2B, hβ1o _ (regTail_ne_zero rA j)
          (fun h ↦ hAB.ne j.succ 0 (by rw [← regTail_apply]; exact h)),
          hβ1o _ (fun h ↦ hAB.ne 0 j.succ (by rw [← regTail_apply]; exact h.symm))
          (regTail_ne_zero rB j), hβ1o c hca hcb, regTail_apply, regTail_apply]

/-- Swaps of the blocks `B l` and `B (l + off)` for `l < k`, controlled by `c` with clean wire
`w_clean`. -/
def levelSwap (c w_clean : Wire n) (w : ℕ) (B : ℕ → QRegister w n) (off : ℕ) : ℕ → List (Step n)
  | 0 => []
  | k + 1 => levelSwap c w_clean w B off k ++ cswapSteps c w_clean w (B k) (B (k + off))

theorem levelSwap_avoids (c w_clean : Wire n) (w : ℕ) (B : ℕ → QRegister w n) (off k : ℕ)
    (v : Wire n) (hc : c ≠ v) (hwc : w_clean ≠ v) (hB : ∀ l, v ∉ Set.range (B l).wires) :
    ∀ s ∈ levelSwap c w_clean w B off k, s.Avoids v := by
  induction k with
  | zero => simp [levelSwap]
  | succ k ih =>
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact ih s hs
    · exact cswapSteps_avoids _ _ _ _ _ v hc hwc (hB _) (hB _) s hs

theorem runList_levelSwap (c w_clean : Wire n) (w : ℕ) (B : ℕ → QRegister w n) (off k : ℕ)
    (hk : k ≤ off)
    (hD : ∀ l l', l < 2 * off → l' < 2 * off → l ≠ l' → (B l).DisjointWires (B l'))
    (hc : ∀ l, c ∉ Set.range (B l).wires) (hwc : c ≠ w_clean)
    (hwB : ∀ l, w_clean ∉ Set.range (B l).wires)
    (β : BitAssignment n) (hw0 : β w_clean = 0) :
    ∃ β', runList (levelSwap c w_clean w B off k) β = some β' ∧
      (∀ v, (∀ l < k, v ∉ Set.range (B l).wires ∧ v ∉ Set.range (B (l + off)).wires) → β' v = β v) ∧
      ∀ l < k, ∀ i, β' (B l i) = β (B (l + off * (β c).val) i) := by
  induction k with
  | zero => exact ⟨β, rfl, fun _ _ ↦ rfl, fun l hl ↦ absurd hl (Nat.not_lt_zero l)⟩
  | succ k ih =>
    obtain ⟨β1, h1, hfr1, h1B⟩ := ih (by omega)
    obtain ⟨β2, h2, hfr2, h2A, h2B⟩ := runList_cswapSteps c w_clean w (B k) (B (k + off))
      (hD _ _ (by omega) (by omega) (by omega)) (hc _) (hc _) hwc (hwB _) (hwB _) β1
      (by rw [hfr1 w_clean fun l _ ↦ ⟨hwB l, hwB _⟩, hw0])
    have hc1 : β1 c = β c := hfr1 c fun l _ ↦ ⟨hc l, hc _⟩
    refine ⟨β2, by rw [levelSwap, runList_append, h1, Option.bind_some, h2],
      fun v hv ↦ by
        rw [hfr2 v (hv k (by omega)).1 (hv k (by omega)).2,
          hfr1 v fun l hl ↦ hv l (by omega)],
      fun l hl i ↦ ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | hl
    · rw [hfr2 _ (not_mem_of_disjoint (hD _ _ (by omega) (by omega) (by omega)) i)
        (not_mem_of_disjoint (hD _ _ (by omega) (by omega) (by omega)) i), h1B l hl i]
    · rw [hl, h2A, hc1, hfr1 _ fun l' hl' ↦
          ⟨not_mem_of_disjoint (hD _ _ (by omega) (by omega) (by omega)) i,
            not_mem_of_disjoint (hD _ _ (by omega) (by omega) (by omega)) i⟩,
        hfr1 _ fun l' hl' ↦
          ⟨not_mem_of_disjoint (hD _ _ (by omega) (by omega) (by omega)) i,
            not_mem_of_disjoint (hD _ _ (by omega) (by omega) (by omega)) i⟩]
      rcases bit_cases (β c) with h | h <;> rw [h]
      · simp
      · rw [one_mul, ← add_assoc, CharTwo.add_self_eq_zero, zero_add,
          show ZMod.val (1 : ZMod 2) = 1 from rfl, mul_one]

/-- Moves block `B v` to position `0`, where `v` is the value of `rc`, using clean wire
`w_clean`. -/
def swapTree (w_clean : Wire n) (w : ℕ) (B : ℕ → QRegister w n) :
    (s : ℕ) → QRegister s n → List (Step n)
  | 0, _ => []
  | s + 1, rc => levelSwap (rc (Fin.last s)) w_clean w B (2 ^ s) (2 ^ s) ++
      swapTree w_clean w B s (rc.slice 0 s (by omega))

theorem cswapSteps_noUnxor (c w_clean : Wire n) (w : ℕ) (rA rB : QRegister w n) :
    ∀ st ∈ cswapSteps c w_clean w rA rB, st.NoUnxor := by
  induction w with
  | zero => simp [cswapSteps]
  | succ w ih =>
    intro st hst
    simp only [cswapSteps, List.cons_append, List.mem_cons, List.nil_append] at hst
    rcases hst with rfl | rfl | rfl | rfl | rfl | hst
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · exact ih _ _ st hst

theorem levelSwap_noUnxor (c w_clean : Wire n) (w : ℕ) (B : ℕ → QRegister w n) (off k : ℕ) :
    ∀ st ∈ levelSwap c w_clean w B off k, st.NoUnxor := by
  induction k with
  | zero => simp [levelSwap]
  | succ k ih =>
    intro st hst
    rcases List.mem_append.mp hst with hst | hst
    · exact ih st hst
    · exact cswapSteps_noUnxor _ _ _ _ _ st hst

theorem swapTree_noUnxor (w_clean : Wire n) (w : ℕ) (B : ℕ → QRegister w n) (s : ℕ)
    (rc : QRegister s n) : ∀ st ∈ swapTree w_clean w B s rc, st.NoUnxor := by
  induction s with
  | zero => simp [swapTree]
  | succ s ih =>
    intro st hst
    rcases List.mem_append.mp hst with hst | hst
    · exact levelSwap_noUnxor _ _ _ _ _ _ st hst
    · exact ih _ st hst

theorem swapTree_avoids (w_clean : Wire n) (w : ℕ) (B : ℕ → QRegister w n) (s : ℕ)
    (rc : QRegister s n) (v : Wire n) (hwc : w_clean ≠ v) (hc : v ∉ Set.range rc.wires)
    (hB : ∀ l, v ∉ Set.range (B l).wires) :
    ∀ st ∈ swapTree w_clean w B s rc, st.Avoids v := by
  induction s with
  | zero => simp [swapTree]
  | succ s ih =>
    intro st hst
    rcases List.mem_append.mp hst with hst | hst
    · exact levelSwap_avoids _ _ _ _ _ _ v (fun h ↦ hc ⟨_, h⟩) hwc hB st hst
    · exact ih _ (not_mem_slice hc _ _ _) st hst

theorem runList_swapTree (w_clean : Wire n) (w : ℕ) (B : ℕ → QRegister w n) (s : ℕ)
    (rc : QRegister s n)
    (hD : ∀ l l', l < 2 ^ s → l' < 2 ^ s → l ≠ l' → (B l).DisjointWires (B l'))
    (hc : ∀ j l, rc j ∉ Set.range (B l).wires)
    (hwrc : w_clean ∉ Set.range rc.wires) (hwB : ∀ l, w_clean ∉ Set.range (B l).wires)
    (β : BitAssignment n) (hw0 : β w_clean = 0) :
    ∃ β', runList (swapTree w_clean w B s rc) β = some β' ∧
      (∀ v, (∀ l, v ∉ Set.range (B l).wires) → β' v = β v) ∧
      ∀ i, β' (B 0 i) = β (B (localIdx rc β) i) := by
  induction s generalizing β with
  | zero =>
    refine ⟨β, rfl, fun _ _ ↦ rfl, fun i ↦ ?_⟩
    rw [show (localIdx rc β : ℕ) = 0 from Nat.lt_one_iff.mp (by simp)]
  | succ s ih =>
    obtain ⟨β1, h1, hfr1, h1B⟩ := runList_levelSwap (rc (Fin.last s)) w_clean w B (2 ^ s) (2 ^ s)
      le_rfl (fun l l' hl hl' ↦ hD l l' (by rw [pow_succ]; omega) (by rw [pow_succ]; omega))
      (hc _) (fun h ↦ hwrc ⟨Fin.last s, h⟩) hwB β hw0
    have hc' : ∀ j l, (rc.slice 0 s (by omega)) j ∉ Set.range (B l).wires := fun j l ↦ by
      rw [QRegister.slice_apply]
      exact hc _ l
    obtain ⟨β2, h2, hfr2, h2B⟩ := ih (rc.slice 0 s (by omega))
      (fun l l' hl hl' ↦ hD l l' (by rw [pow_succ]; omega) (by rw [pow_succ]; omega)) hc'
      (not_mem_slice hwrc 0 s (by omega)) β1 (by rw [hfr1 w_clean fun l _ ↦ ⟨hwB l, hwB _⟩, hw0])
    have hrc : localIdx (rc.slice 0 s (by omega)) β1 = localIdx (rc.slice 0 s (by omega)) β := by
      simp only [localIdx]
      congr 1
      funext j
      exact hfr1 _ fun l _ ↦ ⟨hc' j l, hc' j _⟩
    have hlast : (localIdx (rc.slice s 1 (by omega)) β : ℕ) = (β (rc (Fin.last s))).val := by
      rw [localIdx_val, Fin.sum_univ_one, QRegister.slice_apply]
      simp only [Fin.val_zero, pow_zero, mul_one, add_zero]
      rfl
    refine ⟨β2, by rw [swapTree, runList_append, h1, Option.bind_some, h2],
      fun v hv ↦ by rw [hfr2 v hv, hfr1 v fun l _ ↦ ⟨hv l, hv _⟩],
      fun i ↦ ?_⟩
    rw [h2B, hrc, h1B _ (localIdx _ β).isLt, localIdx_val_split rc s 1 rfl β, hlast]

variable {n : ℕ}

/-- Little-endian bits of the table entry `f x mod 2^w`. -/
def tableBits (w : ℕ) (f : ℕ → ℕ) (x : ℕ) : BitAssignment w :=
  fun i ↦ ((f x / 2 ^ (i : ℕ) % 2 : ℕ) : ZMod 2)

theorem tableBits_eq (w : ℕ) (f : ℕ → ℕ) (x : ℕ) :
    tableBits w f x = basisBits w ⟨f x % 2 ^ w, Nat.mod_lt _ (by positivity)⟩ := by
  funext i
  have h : 2 ^ w = 2 ^ (i : ℕ) * 2 ^ (w - i) := by rw [← pow_add, Nat.add_sub_cancel' i.isLt.le]
  rw [basisBits_mk_apply, tableBits, h, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))]

theorem ctrlNe_none (w : Wire n) : CtrlNe none w := fun _ h ↦ (Option.some_ne_none _ h.symm).elim

/-- The entries `f (l + 2^s h)` for `l < 2^s`, `K + 1` bits each, laid out side by side. -/
def wideTable (s K : ℕ) (f : ℕ → ℕ) (h : ℕ) : BitAssignment (2 ^ s * (K + 1)) :=
  fun p ↦ tableBits (K + 1) f ((p : ℕ) / (K + 1) + 2 ^ s * h) ⟨p % (K + 1), Nat.mod_lt _ K.succ_pos⟩

/-- Block `l mod 2^s` of `w` consecutive wires of `rD`. -/
def dataBlock (s w : ℕ) (rD : QRegister (2 ^ s * w) n) (l : ℕ) : QRegister w n :=
  rD.slice (l % 2 ^ s * w) w (by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ (Nat.mod_lt _ (by positivity)))

theorem dataBlock_disjoint (s w : ℕ) (rD : QRegister (2 ^ s * w) n) {l l' : ℕ} (hl : l < 2 ^ s)
    (hl' : l' < 2 ^ s) (h : l ≠ l') : (dataBlock s w rD l).DisjointWires (dataBlock s w rD l') := by
  rw [QRegister.disjoint_iff]
  intro i j heq
  rw [dataBlock, dataBlock, QRegister.slice_apply, QRegister.slice_apply] at heq
  have hv := congrArg Fin.val (rD.wires.injective heq)
  simp only [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hl'] at hv
  have hw : 0 < w := (Nat.zero_le _).trans_lt i.isLt
  apply h
  have hd := congrArg (· / w) hv
  simp only [add_comm _ (i : ℕ), add_comm _ (j : ℕ), Nat.add_mul_div_right _ _ hw,
    Nat.div_eq_of_lt i.isLt, Nat.div_eq_of_lt j.isLt, zero_add] at hd
  exact hd

theorem writeReg_wideTable_dataBlock (β : BitAssignment n) (s K : ℕ) (f : ℕ → ℕ)
    (rD : QRegister (2 ^ s * (K + 1)) n) (h l : ℕ) (hl : l < 2 ^ s) (i : Fin (K + 1)) :
    writeReg β rD (wideTable s K f h) (dataBlock s (K + 1) rD l i) =
      tableBits (K + 1) f (l + 2 ^ s * h) i := by
  have hd : (l * (K + 1) + i) / (K + 1) = l := by
    rw [add_comm, Nat.add_mul_div_right _ _ K.succ_pos, Nat.div_eq_of_lt i.isLt, zero_add]
  have hm : (l * (K + 1) + i) % (K + 1) = i := by
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
  rw [dataBlock, QRegister.slice_apply, writeReg_apply_reg, wideTable]
  simp only [Nat.mod_eq_of_lt hl, hd, hm]

/-- Sub-Toffoli (`4T/0T`) select-swap lookup and Gidney ripple-carry addition on `2 * k` data wires
(`k` output wires `b` followed by `k` input wires `x`), using `and4t` (`4 T`) + `unand` (`0 T`)
at every lookup, swap, and addition carry step (`0` `.TOFF` gates). -/
def equalTableAddCore (K s : ℕ) (f : ℕ → ℕ) (rD : QRegister (2 ^ s * (K + 1)) n)
    (rXl : QRegister s n) (rXh rW : QRegister (K + 1 - s) n) (rB : QRegister (K + 1) n)
    (ci : Wire n) (rC : QRegister K n) : List (Step n) :=
  lookupSteps _ rD (K + 1 - s) none rXh rW (wideTable s K f) ++
    swapTree ci (K + 1) (dataBlock s (K + 1) rD) s rXl ++
    rippleSteps K (dataBlock s (K + 1) rD 0) rB ci rC ++
    (swapTree ci (K + 1) (dataBlock s (K + 1) rD) s rXl).reverse.map Step.inv ++
    lookupSteps _ rD (K + 1 - s) none rXh rW (wideTable s K f)

theorem runList_equalTableAddCore (K s : ℕ) (f : ℕ → ℕ) (rD : QRegister (2 ^ s * (K + 1)) n)
    (rXl : QRegister s n) (rXh rW : QRegister (K + 1 - s) n) (rB : QRegister (K + 1) n)
    (ci : Wire n) (rC : QRegister K n)
    (hDl : rD.DisjointWires rXl) (hDh : rD.DisjointWires rXh) (hDW : rD.DisjointWires rW)
    (hDB : rD.DisjointWires rB) (hDC : rD.DisjointWires rC) (hlB : rXl.DisjointWires rB)
    (hhW : rXh.DisjointWires rW) (hhB : rXh.DisjointWires rB) (hWB : rW.DisjointWires rB)
    (hCB : rC.DisjointWires rB) (hiD : ci ∉ Set.range rD.wires) (hiXl : ci ∉ Set.range rXl.wires)
    (hiB : ci ∉ Set.range rB.wires) (hiC : ci ∉ Set.range rC.wires) (β : BitAssignment n)
    (hD : ∀ i, β (rD i) = 0) (hW : ∀ i, β (rW i) = 0) (hci : β ci = 0) (hC : ∀ i, β (rC i) = 0) :
    runList (equalTableAddCore K s f rD rXl rXh rW rB ci rC) β =
      some (writeReg β rB (basisBits (K + 1)
        ⟨(f ((localIdx rXl β : ℕ) + 2 ^ s * (localIdx rXh β : ℕ)) % 2 ^ (K + 1) +
          (localIdx rB β : ℕ)) % 2 ^ (K + 1), Nat.mod_lt _ (by positivity)⟩)) := by
  set B := dataBlock s (K + 1) rD with hBdef
  set S := swapTree ci (K + 1) B s rXl with hS
  have hnB : ∀ {v}, v ∉ Set.range rD.wires → ∀ l, v ∉ Set.range (B l).wires :=
    fun hv _ ↦ not_mem_slice hv _ _ _
  have hlook := fun β' ↦ runList_lookupSteps _ rD (K + 1 - s) none rXh rW (wideTable s K f) hhW
    (QRegister.disjoint_comm.mp hDh) (QRegister.disjoint_comm.mp hDW)
    (fun _ ↦ ctrlNe_none _) (fun _ ↦ ctrlNe_none _) (fun _ ↦ ctrlNe_none _) β'
  set x := (localIdx rXl β : ℕ) + 2 ^ s * (localIdx rXh β : ℕ) with hx
  set β1 := writeReg β rD (wideTable s K f (localIdx rXh β)) with hβ1
  have h1 : runList (lookupSteps _ rD (K + 1 - s) none rXh rW (wideTable s K f)) β = some β1 := by
    rw [hlook β hW]
    simp only [hD, ctrlVal, zero_add, one_mul]
    rfl
  have hb1 : ∀ v, v ∉ Set.range rD.wires → β1 v = β v := fun v hv ↦
    writeReg_apply_of_not_mem _ _ _ _ hv
  obtain ⟨β2, h2, hfr2_B, h2B⟩ := runList_swapTree ci (K + 1) B s rXl
    (fun l l' hl hl' h ↦ dataBlock_disjoint s (K + 1) rD hl hl' h)
    (fun j ↦ hnB (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDl) j))
    hiXl (hnB hiD) β1 (by rw [hb1 _ hiD, hci])
  have hfr2 : ∀ v, v ∉ Set.range rD.wires → β2 v = β1 v := fun v hv ↦ hfr2_B v (hnB hv)
  have hB0 : localIdx (B 0) β2 = ⟨f x % 2 ^ (K + 1), Nat.mod_lt _ (by positivity)⟩ := by
    have hl := (localIdx rXl β).isLt
    have : (fun i ↦ β2 (B 0 i)) = tableBits (K + 1) f x := funext fun i ↦ by
      rw [h2B, localIdx_writeReg_of_disjoint _ _ _ hDl, hβ1,
        writeReg_wideTable_dataBlock _ _ _ _ _ _ _ hl]
    simp only [localIdx, this, tableBits_eq, basisBitsEquiv_symm_basisBits]
  have hrB : localIdx rB β2 = localIdx rB β := by
    simp only [localIdx]
    congr 1
    funext i
    rw [hfr2 _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDB) i),
      hb1 _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDB) i)]
  set γ := basisBits (K + 1) ⟨(f x % 2 ^ (K + 1) + (localIdx rB β : ℕ)) % 2 ^ (K + 1),
    Nat.mod_lt _ (by positivity)⟩ with hγ
  have h3 : runList (rippleSteps K (B 0) rB ci rC) β2 = some (writeReg β2 rB γ) := by
    rw [runList_rippleSteps K (B 0) rB ci rC (hDB.compose_left _) (hDC.compose_left _)
      (QRegister.disjoint_comm.mp hCB) (hnB hiD 0) hiB hiC β2 (fun i ↦ by
        rw [hfr2 _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDC) i),
          hb1 _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDC) i), hC]),
      hB0, hrB, hfr2 _ hiD, hb1 _ hiD, hci, ZMod.val_zero, add_zero]
  have h4 : runList (S.reverse.map Step.inv) (writeReg β2 rB γ) = some (writeReg β1 rB γ) := by
    rw [runList_writeReg_of_avoids _ rB (fun st hst i ↦ by
        obtain ⟨st', hst', rfl⟩ := List.mem_map.mp hst
        exact Step.avoids_inv (swapTree_avoids ci (K + 1) B s rXl _
          (fun h ↦ hiB ⟨i, h.symm⟩)
          (not_mem_of_disjoint (QRegister.disjoint_comm.mp hlB) i)
          (hnB (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDB) i))
          st' (List.mem_reverse.mp hst'))),
      runList_inv (swapTree_noUnxor ci (K + 1) B s rXl) h2, Option.map_some]
  rw [equalTableAddCore, runList_append, runList_append, runList_append, runList_append, h1,
    Option.bind_some, ← hS, h2, Option.bind_some, h3, Option.bind_some, h4, Option.bind_some,
    hlook _ (fun i ↦ by
      rw [writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hWB i),
        hb1 _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDW) i), hW])]
  simp only [localIdx_writeReg_of_disjoint _ _ _ (QRegister.disjoint_comm.mp hhB),
    hβ1, localIdx_writeReg_of_disjoint _ _ _ hDh,
    writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hDB _), writeReg_apply_reg, ctrlVal,
    one_mul, CharTwo.add_self_eq_zero]
  rw [writeReg_comm _ rB rD (QRegister.disjoint_comm.mp hDB), writeReg_writeReg,
    show (fun _ : Fin (2 ^ s * (K + 1)) ↦ (0 : ZMod 2)) = fun i ↦ β (rD i) from
      funext fun i ↦ (hD i).symm, writeReg_self]

theorem writeReg_eq_of_eqOn {k : ℕ} (β β' : BitAssignment n) (r : QRegister k n)
    (h : ∀ w ∉ Set.range r.wires, β' w = β w) : writeReg β r (fun i ↦ β' (r i)) = β' := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    rw [writeReg_apply_reg]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw, h w hw]

theorem eq_zero_of_localIdx_eq_zero {k : ℕ} (r : QRegister k n) (β : BitAssignment n)
    (h : localIdx r β = 0) (i : Fin k) : β (r i) = 0 := by
  have hi := congrArg (fun j ↦ basisBits k j i) h
  simp only [localIdx, basisBits_basisBitsEquiv_symm] at hi
  rw [hi, basisBits_eq_div_mod]
  simp

/-- Sub-Toffoli select-swap QROM lookup and Gidney ripple-carry addition on `2 * k` data wires. -/
def equalTableAddSteps (k s : ℕ) (hs : s ≤ k) (f : ℕ → ℕ) :
    QRegister (2 * k) n → QRegister (2 ^ s * k + k) n → List (Step n) :=
  match k with
  | 0 => fun _ _ => []
  | K + 1 => fun rData rAnc =>
      equalTableAddCore K s f (rAnc.slice 0 (2 ^ s * (K + 1)) (by omega))
        (rData.slice (K + 1) s (by omega)) (rData.slice (K + 1 + s) (K + 1 - s) (by omega))
        (rAnc.slice (2 ^ s * (K + 1)) (K + 1 - s) (by omega)) (rData.slice 0 (K + 1) (by omega))
        (rAnc ⟨2 ^ s * (K + 1), by omega⟩)
        (rAnc.slice (2 ^ s * (K + 1) + 1) K (by omega))

theorem runList_equalTableAddSteps (k s : ℕ) (hs : s ≤ k) (f : ℕ → ℕ)
    (rData : QRegister (2 * k) n) (rAnc : QRegister (2 ^ s * k + k) n)
    (hdisj : rData.DisjointWires rAnc) (σ : Equiv.Perm (Fin (2 ^ (2 * k))))
    (hσ : ∀ j, (σ j : ℕ) =
      (j % 2 ^ k + f (j / 2 ^ k)) % 2 ^ k + 2 ^ k * (j / 2 ^ k))
    (β : BitAssignment n) (hβ : localIdx rAnc β = 0) :
    runList (equalTableAddSteps k s hs f rData rAnc) β =
      some (writeReg β rData (basisBits (2 * k) (σ (localIdx rData β)))) := by
  cases k with
  | zero =>
    have h : σ (localIdx rData β) = localIdx rData β := Fin.ext (by
      rw [hσ]
      simp only [pow_zero, Nat.mod_one, Nat.div_one, one_mul, zero_add])
    rw [equalTableAddSteps, runList_nil, h, basisBits_basisBitsEquiv_symm, writeReg_self]
  | succ K =>
    have hclean := eq_zero_of_localIdx_eq_zero rAnc β hβ
    have hDA : ∀ {a b : ℕ} (r : QRegister a (2 * (K + 1)))
        (r' : QRegister b (2 ^ s * (K + 1) + (K + 1))),
        (rAnc.compose r').DisjointWires (rData.compose r) := fun _ _ ↦
      QRegister.disjoint_comm.mp ((hdisj.compose_left _).compose_right _)
    have hx : (localIdx (rData.slice (K + 1) (K + 1) (by omega)) β : ℕ) =
        (localIdx (rData.slice (K + 1) s (by omega)) β : ℕ) +
          2 ^ s * (localIdx (rData.slice (K + 1 + s) (K + 1 - s) (by omega)) β : ℕ) := by
      rw [localIdx_val_split _ s (K + 1 - s) (by omega)]
      simp only [localIdx_slice_slice, add_zero]
    have hXB : (rData.slice 0 (K + 1) (by omega)).DisjointWires
        (rData.slice (K + 1) (K + 1) (by omega)) :=
      QRegister.slice_disjoint_of_le rData 0 (K + 1) (K + 1) (K + 1)
        (by omega) (by omega) (by omega)
    rw [equalTableAddSteps, runList_equalTableAddCore K s f _ _ _ _ _ _ _ (hDA _ _) (hDA _ _)
      (QRegister.slice_disjoint_of_le rAnc _ _ _ _ (by omega) (by omega) (by omega)) (hDA _ _)
      (QRegister.slice_disjoint_of_le rAnc _ _ _ _ (by omega) (by omega) (by omega))
      (QRegister.disjoint_comm.mp
        (QRegister.slice_disjoint_of_le rData _ _ _ _ (by omega) (by omega) (by omega)))
      (QRegister.disjoint_comm.mp (hDA _ _))
      (QRegister.disjoint_comm.mp
        (QRegister.slice_disjoint_of_le rData _ _ _ _ (by omega) (by omega) (by omega)))
      (hDA _ _) (hDA _ _)
      (apply_not_mem_slice rAnc _ 0 _ (by omega) (Or.inr (by simp)))
      (fun ⟨_, h⟩ ↦ hdisj.ne _ _ h)
      (fun ⟨_, h⟩ ↦ hdisj.ne _ _ h)
      (apply_not_mem_slice rAnc _ (2 ^ s * (K + 1) + 1) K (by omega) (Or.inl (by dsimp; omega)))
      β (fun _ ↦ hclean _) (fun _ ↦ hclean _) (hclean _) (fun _ ↦ hclean _), ← hx]
    refine congrArg some ?_
    rw [← writeReg_eq_of_eqOn β (writeReg β (rData.slice 0 (K + 1) (by omega)) _) rData
      fun w hw ↦ writeReg_apply_of_not_mem _ _ _ _ fun ⟨i, h⟩ ↦ hw ⟨_, h⟩]
    congr 1
    rw [← basisBits_basisBitsEquiv_symm (2 * (K + 1)) (fun p ↦ _)]
    congr 1
    apply Fin.ext
    have hB := (localIdx (rData.slice 0 (K + 1) (by omega)) β).isLt
    rw [hσ, localIdx_val_split rData (K + 1) (K + 1) (by omega) β, ← localIdx,
      localIdx_val_split rData (K + 1) (K + 1) (by omega), localIdx_writeReg,
      basisBitsEquiv_symm_basisBits, localIdx_writeReg_of_disjoint _ _ _ hXB,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hB, Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt hB]
    simp only [zero_add, Nat.mod_add_mod]
    rw [add_comm (f _)]


theorem andCount_ctrlFlip (c : Option (Wire n)) (t : Wire n) :
    (ctrlFlip c t).andCount = 0 := by
  cases c <;> rfl

theorem andCount_xorSteps (c : Option (Wire n)) (w : ℕ) (rY : QRegister w n)
    (d : BitAssignment w) : ((xorSteps c w rY d).map Step.andCount).sum = 0 := by
  induction w with
  | zero => rfl
  | succ w ih =>
    rw [xorSteps, List.map_append, List.sum_append, ih]
    split_ifs <;> simp [andCount_ctrlFlip]

theorem andCount_andNotSteps (c : Option (Wire n)) (t c' : Wire n) :
    ((andNotSteps c t c').map Step.andCount).sum ≤ 1 := by
  cases c <;> simp [andNotSteps, Step.andCount]

theorem andCount_unAndSteps (c : Option (Wire n)) (t c' : Wire n) :
    ((unAndSteps c t c').map Step.andCount).sum = 0 := by
  cases c <;> rfl

theorem andCount_lookupSteps (w : ℕ) (rY : QRegister w n) (m : ℕ)
    (c : Option (Wire n)) (rX rW : QRegister m n) (T : ℕ → BitAssignment w) :
    ((lookupSteps w rY m c rX rW T).map Step.andCount).sum ≤ 2 ^ m - 1 := by
  induction m generalizing c T with
  | zero => simp [lookupSteps, andCount_xorSteps]
  | succ m ih =>
    rw [lookupSteps]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, andCount_ctrlFlip, andCount_unAndSteps]
    have h0 := andCount_andNotSteps c (rX 0) (rW 0)
    have h1 := ih (some (rW 0)) (regTail rX) (regTail rW) (fun j ↦ T (2 * j))
    have h2 := ih (some (rW 0)) (regTail rX) (regTail rW) (fun j ↦ T (2 * j + 1))
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    have hm1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega

theorem andCount_rippleSteps (k : ℕ) (rA rB : QRegister (k + 1) n) (ci : Wire n)
    (rC : QRegister k n) : ((rippleSteps k rA rB ci rC).map Step.andCount).sum = k := by
  induction k generalizing ci with
  | zero => rfl
  | succ k ih =>
    rw [rippleSteps, List.map_append, List.map_append, List.sum_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Step.andCount]
    omega

theorem andCount_equalTableAddSteps_zero (k : ℕ) (f : ℕ → ℕ)
    (rData : QRegister (2 * k) n) (rAnc : QRegister (2 ^ 0 * k + k) n) :
    ((equalTableAddSteps k 0 (Nat.zero_le k) f rData rAnc).map Step.andCount).sum ≤
      2 * 2 ^ k + k := by
  cases k with
  | zero => simp [equalTableAddSteps]
  | succ K =>
    unfold equalTableAddSteps equalTableAddCore
    simp only [swapTree, List.reverse_nil, List.map_nil, List.append_nil,
      List.map_append, List.sum_append, Nat.sub_zero]
    have h1 := andCount_lookupSteps (2 ^ 0 * (K + 1)) (rAnc.slice 0 (2 ^ 0 * (K + 1)) (by omega))
      (K + 1) none (rData.slice (K + 1 + 0) (K + 1) (by omega))
      (rAnc.slice (2 ^ 0 * (K + 1)) (K + 1) (by omega)) (wideTable 0 K f)
    have h2 := andCount_rippleSteps K
      (dataBlock 0 (K + 1) (rAnc.slice 0 (2 ^ 0 * (K + 1)) (by omega)) 0)
      (rData.slice 0 (K + 1) (by omega)) (rAnc ⟨2 ^ 0 * (K + 1), by omega⟩)
      (rAnc.slice (2 ^ 0 * (K + 1) + 1) K (by omega))
    omega


end TableLookupSteps

end QuantumComputation.Specs

/-! END GOOGLE-DERIVED -/

namespace QuantumComputation.Specs
namespace AliasTable
open Finset

/-- Vose's algorithm on a list `S` of active slots with residual masses `r`, by recursion on a fuel
bound (the number of active slots). -/
def aliasBuild (M : ℕ) : ℕ → List ℕ → (ℕ → ℕ) → (ℕ → ℕ × ℕ)
  | 0, _, _ => fun i => (0, i)
  | k + 1, S, r =>
    match S.find? (fun j => decide (r j ≤ M)) with
    | none => fun i => (0, i)
    | some s =>
      match (S.erase s).find? (fun j => decide (M ≤ r j)) with
      | none => Function.update (aliasBuild M k (S.erase s) r) s (0, s)
      | some l =>
        Function.update
          (aliasBuild M k (S.erase s) (Function.update r l (r l + r s - M))) s
          (if r s < M then (r s, l) else (0, s))

/-- Alias table for `N` slots, each of `M` sub-slots, for counts `m j` (j < N) summing to `N * M`.
Entry `i` is `(K_i, a_i)`: sub-slot `s` of slot `i` goes to `i` if `s < K_i`, else to `a_i`. -/
def aliasTable (M N : ℕ) (m : ℕ → ℕ) : ℕ → ℕ × ℕ :=
  aliasBuild M N (List.range N) m

def aliasOut (M N : ℕ) (m : ℕ → ℕ) (i s : ℕ) : ℕ :=
  if s < (aliasTable M N m i).1 then i else (aliasTable M N m i).2

/-- Number of sub-slots of slot `i` sent to `j`. -/
def contrib (M : ℕ) (T : ℕ → ℕ × ℕ) (i j : ℕ) : ℕ :=
  (if i = j then (T i).1 else 0) + (if (T i).2 = j then M - (T i).1 else 0)

def Good (M : ℕ) (S : List ℕ) (r : ℕ → ℕ) (T : ℕ → ℕ × ℕ) : Prop :=
  (∀ i ∈ S, (T i).1 < M ∧ (T i).2 ∈ S) ∧
    ∀ j ∈ S, r j = (S.map (fun i ↦ contrib M T i j)).sum

lemma sum_erase (S : List ℕ) (s : ℕ) (hs : s ∈ S) (f : ℕ → ℕ) :
    (S.map f).sum = f s + ((S.erase s).map f).sum := by
  have := ((List.perm_cons_erase hs).map f).sum_eq
  simpa using this

lemma sum_lt_of_lt (M : ℕ) (r : ℕ → ℕ) : ∀ S : List ℕ, S ≠ [] → (∀ j ∈ S, r j < M) →
    (S.map r).sum < S.length * M := by
  intro S
  induction S with
  | nil => simp
  | cons a t ih =>
    intro _ h
    have ha := h a (by simp)
    have h2 : ∀ j ∈ t, r j < M := fun j hj ↦ h j (by simp [hj])
    by_cases ht : t = []
    · subst ht; simpa using ha
    · have := ih ht h2
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

lemma sum_gt_of_gt (M : ℕ) (r : ℕ → ℕ) : ∀ S : List ℕ, S ≠ [] → (∀ j ∈ S, M < r j) →
    S.length * M < (S.map r).sum := by
  intro S
  induction S with
  | nil => simp
  | cons a t ih =>
    intro _ h
    have ha := h a (by simp)
    have h2 : ∀ j ∈ t, M < r j := fun j hj ↦ h j (by simp [hj])
    by_cases ht : t = []
    · subst ht; simpa using ha
    · have := ih ht h2
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

lemma good_step (M : ℕ) (S : List ℕ) (r r' : ℕ → ℕ) (T' : ℕ → ℕ × ℕ) (s : ℕ) (e : ℕ × ℕ)
    (hnd : S.Nodup) (hs : s ∈ S) (hG : Good M (S.erase s) r' T')
    (he1 : e.1 < M) (he2 : e.2 ∈ S)
    (hr1 : ∀ j ∈ S.erase s, r j = r' j + if e.2 = j then M - e.1 else 0)
    (hr2 : r s = e.1 + if e.2 = s then M - e.1 else 0) :
    Good M S r (Function.update T' s e) := by
  have hne : ∀ i ∈ S.erase s, i ≠ s := fun i hi ↦ ((hnd.mem_erase_iff).1 hi).1
  refine ⟨?_, ?_⟩
  · intro i hi
    by_cases his : i = s
    · subst his; simpa using And.intro he1 he2
    · have hi' : i ∈ S.erase s := (hnd.mem_erase_iff).2 ⟨his, hi⟩
      have := hG.1 i hi'
      simp only [Function.update_of_ne his]
      exact ⟨this.1, List.mem_of_mem_erase this.2⟩
  · intro j hj
    rw [sum_erase S s hs]
    have hcongr : ((S.erase s).map (fun i ↦ contrib M (Function.update T' s e) i j)).sum
        = ((S.erase s).map (fun i ↦ contrib M T' i j)).sum := by
      congr 1
      apply List.map_congr_left
      intro i hi
      simp [contrib, Function.update_of_ne (hne i hi)]
    rw [hcongr]
    by_cases hjs : j = s
    · subst hjs
      have h0 : ((S.erase j).map (fun i ↦ contrib M T' i j)).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
        have h2 := (hG.1 i hi).2
        have hij := hne i hi
        have h3 : (T' i).2 ≠ j := fun h ↦ hne _ h2 h
        simp [contrib, hij, h3]
      rw [h0, hr2]
      simp [contrib]
    · have hj' : j ∈ S.erase s := (hnd.mem_erase_iff).2 ⟨hjs, hj⟩
      have h1 := hG.2 j hj'
      have h2 := hr1 j hj'
      rw [← h1] at *
      rw [h2]
      simp [contrib, Ne.symm hjs]
      omega

theorem build_good (M : ℕ) (hM : 0 < M) : ∀ (k : ℕ) (S : List ℕ) (r : ℕ → ℕ), S.Nodup →
    S.length = k → (S.map r).sum = k * M → Good M S r (aliasBuild M k S r) := by
  intro k
  induction k with
  | zero =>
    intro S r _ hlen _
    have : S = [] := List.length_eq_zero_iff.1 hlen
    subst this
    simp [Good]
  | succ k ih =>
    intro S r hnd hlen hsum
    have hne : S ≠ [] := by
      rintro rfl; simp at hlen
    have hex : ∃ s ∈ S, r s ≤ M := by
      by_contra h
      push Not at h
      have := sum_gt_of_gt M r S hne h
      rw [hlen, hsum] at this
      exact lt_irrefl _ this
    simp only [aliasBuild]
    split
    · rename_i hs
      exfalso
      obtain ⟨j, hj, hjr⟩ := hex
      have := List.find?_eq_none.1 hs j hj
      simp [hjr] at this
    · rename_i s hs
      have hsS : s ∈ S := List.mem_of_find?_eq_some hs
      have hsr : r s ≤ M := by simpa using List.find?_some hs
      have hndE : (S.erase s).Nodup := hnd.erase s
      have hlenE : (S.erase s).length = k := by
        rw [List.length_erase_of_mem hsS, hlen]; rfl
      have hsumS := sum_erase S s hsS r
      have hsM : (k + 1) * M = k * M + M := by ring
      split
      · rename_i hl
        have hk : k = 0 := by
          by_contra hk0
          have hneE : S.erase s ≠ [] := by
            intro h; rw [h] at hlenE; simp at hlenE; omega
          have hlt : ∀ j ∈ S.erase s, r j < M := by
            intro j hj
            have := List.find?_eq_none.1 hl j hj
            simpa using this
          have := sum_lt_of_lt M r _ hneE hlt
          rw [hlenE] at this
          omega
        subst hk
        have hE : S.erase s = [] := List.length_eq_zero_iff.1 hlenE
        have hrs : r s = M := by
          rw [hE] at hsumS
          simp at hsumS hsum
          omega
        have hG := ih (S.erase s) r hndE hlenE (by rw [hE]; simp)
        refine good_step M S r r _ s (0, s) hnd hsS hG (by simpa using hM) hsS ?_ ?_
        · intro j hj; rw [hE] at hj; simp at hj
        · simp [hrs]
      · rename_i l hl
        have hlE : l ∈ S.erase s := List.mem_of_find?_eq_some hl
        have hlM : M ≤ r l := by simpa using List.find?_some hl
        have hls : l ≠ s := ((hnd.mem_erase_iff).1 hlE).1
        have hlS : l ∈ S := List.mem_of_mem_erase hlE
        have hsumE := sum_erase (S.erase s) l hlE r
        have hsumE' := sum_erase (S.erase s) l hlE (Function.update r l (r l + r s - M))
        have hndEE : ((S.erase s).erase l).Nodup := hndE.erase l
        have hW : (((S.erase s).erase l).map (Function.update r l (r l + r s - M))).sum
            = (((S.erase s).erase l).map r).sum := by
          congr 1
          apply List.map_congr_left
          intro j hj
          have : j ≠ l := ((hndE.mem_erase_iff).1 hj).1
          simp [Function.update_of_ne this]
        have hsum' : ((S.erase s).map (Function.update r l (r l + r s - M))).sum = k * M := by
          rw [hsumE', hW]
          simp only [Function.update_self]
          omega
        have hG := ih (S.erase s) (Function.update r l (r l + r s - M)) hndE hlenE hsum'
        have hrl : ∀ j ∈ S.erase s, Function.update r l (r l + r s - M) j
            = if j = l then r l + r s - M else r j := by
          intro j _
          by_cases h : j = l
          · subst h; simp
          · simp [h]
        by_cases hlt : r s < M
        · simp only [hlt, ite_true]
          refine good_step M S r _ _ s (r s, l) hnd hsS hG hlt hlS ?_ ?_
          · intro j hj
            rw [hrl j hj]
            by_cases h : j = l
            · subst h; simp; omega
            · simp [h, Ne.symm h]
          · simp [hls]
        · simp only [hlt, ite_false]
          have hrs : r s = M := by omega
          refine good_step M S r _ _ s (0, s) hnd hsS hG (by simpa using hM) hsS ?_ ?_
          · intro j hj
            rw [hrl j hj]
            have hjs : s ≠ j := (Ne.symm ((hnd.mem_erase_iff).1 hj).1)
            by_cases h : j = l
            · subst h; simp [hjs]; omega
            · simp [h, hjs]
          · simp [hrs]

lemma list_range_sum (f : ℕ → ℕ) (N : ℕ) : ((List.range N).map f).sum = ∑ i ∈ range N, f i := by
  induction N with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

lemma aliasTable_good (M N : ℕ) (m : ℕ → ℕ) (hM : 0 < M)
    (hsum : ∑ j ∈ range N, m j = N * M) :
    Good M (List.range N) m (aliasTable M N m) :=
  build_good M hM N (List.range N) m (List.nodup_range) (by simp)
    (by rw [list_range_sum]; exact hsum)

theorem aliasTable_lt (M N : ℕ) (m : ℕ → ℕ) (hM : 0 < M) (hsum : ∑ j ∈ range N, m j = N * M)
    (i : ℕ) (hi : i < N) : (aliasTable M N m i).1 < M ∧ (aliasTable M N m i).2 < N := by
  have := (aliasTable_good M N m hM hsum).1 i (List.mem_range.2 hi)
  simpa using this

lemma card_row (M N : ℕ) (m : ℕ → ℕ) (i j : ℕ) (hK : (aliasTable M N m i).1 ≤ M) :
    ((range M).filter (fun s ↦ aliasOut M N m i s = j)).card = contrib M (aliasTable M N m) i j := by
  rw [Finset.card_filter, ← Finset.sum_range_add_sum_Ico _ hK]
  have h1 : ∑ s ∈ range (aliasTable M N m i).1, (if aliasOut M N m i s = j then 1 else 0)
      = if i = j then (aliasTable M N m i).1 else 0 := by
    rw [Finset.sum_congr rfl (g := fun _ ↦ if i = j then 1 else 0)]
    · simp
    · intro s hs
      have := Finset.mem_range.1 hs
      simp [aliasOut, this]
  have h2 : ∑ s ∈ Ico (aliasTable M N m i).1 M, (if aliasOut M N m i s = j then 1 else 0)
      = if (aliasTable M N m i).2 = j then M - (aliasTable M N m i).1 else 0 := by
    rw [Finset.sum_congr rfl (g := fun _ ↦ if (aliasTable M N m i).2 = j then 1 else 0)]
    · simp
    · intro s hs
      have := (Finset.mem_Ico.1 hs).1
      simp [aliasOut, not_lt.2 this]
  rw [h1, h2]
  rfl

theorem aliasOut_card (M N : ℕ) (m : ℕ → ℕ) (hM : 0 < M) (hsum : ∑ j ∈ range N, m j = N * M)
    (j : ℕ) (hj : j < N) :
    ((range N ×ˢ range M).filter (fun p ↦ aliasOut M N m p.1 p.2 = j)).card = m j := by
  have hG := (aliasTable_good M N m hM hsum).2 j (List.mem_range.2 hj)
  rw [hG, list_range_sum, Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.card_filter]
  exact card_row M N m i j (aliasTable_lt M N m hM hsum i (Finset.mem_range.1 hi)).1.le

/-
#eval (List.range 4).map (aliasTable 4 4 (fun j ↦ [1, 7, 3, 5].getD j 0))
-/

end AliasTable
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

/-
The next block is this repository's `QuantumSolutions/BlockEncoding/PreparePauliLCU.lean`, lines 1196 to 1307, with the
namespace `SelectPauliSteps` renamed to `TableLookupSteps`.
-/
/-! ### General bridge for `RealizesCleanSubroutine`

From a Kraus lower bound `R` of `P` whose action on every clean basis ket is that of the embedded
unitary `U`, conclude `RealizesCleanSubroutine`. Not specific to `SELECT`; stated for any
registers, any `U`. The final step is Google's `TableLookupSteps.realizesCleanSubroutine_of_lowerKraus`
(Arcsin solution), which needs the matrix identity `Π₀ R = Π₀ E Π₀`. The new content is that this
identity follows from the ket-level statement plus the contraction bound `Rᴴ R ≤ 1` that
`LowerKraus` carries: `R` is isometric on the clean subspace, hence maps its orthogonal
complement into the orthogonal complement of the image `E`(clean) = clean. -/
namespace CleanSubroutineBridge

open Operator Matrix QProg Function TableLookupSteps HermitianMat
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

namespace AliasPrepImpl

open TableLookupSteps TableLookupSteps.Step Function
open scoped Matrix ComplexOrder MatrixOrder

variable {n : ℕ}

/-! ### Comparator core

Copied from this repository's `QuantumSolutions/Arithmetic/Comparator.lean` (lines 103 to 128, 194 to 233, 235 to 300 and
359 to 433), with the namespace `ArcsinImpl` renamed to `TableLookupSteps`. -/

theorem sub_arith (P x y : ℕ) (hx : x < P) (hy : y < P) :
    (y + (x + 2 * P - y) % (2 * P)) % (2 * P) = x := by
  by_cases h : y ≤ x
  · have e : (x + 2 * P - y) % (2 * P) = x - y := by
      rw [show x + 2 * P - y = (x - y) + 2 * P by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [e, show y + (x - y) = x by omega, Nat.mod_eq_of_lt (by omega)]
  · have e : (x + 2 * P - y) % (2 * P) = x + 2 * P - y := Nat.mod_eq_of_lt (by omega)
    rw [e, show y + (x + 2 * P - y) = x + 2 * P by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]

/-- The bit `P` of `x - y` modulo `2 * P` is the borrow `[x < y]`. -/
theorem borrow_arith (P x y : ℕ) (hP : 0 < P) (hx : x < P) (hy : y < P) :
    (x + 2 * P - y) % (2 * P) / P % 2 = if x < y then 1 else 0 := by
  by_cases h : x < y
  · simp only [h, ↓reduceIte]
    have e : (x + 2 * P - y) % (2 * P) = x + 2 * P - y := Nat.mod_eq_of_lt (by omega)
    have e2 : (x + 2 * P - y) / P = 1 := by
      rw [show x + 2 * P - y = (x + P - y) + P * 1 by omega, Nat.add_mul_div_left _ _ hP,
        Nat.div_eq_of_lt (by omega)]
    rw [e, e2]
  · simp only [h, ↓reduceIte]
    have e : (x + 2 * P - y) % (2 * P) = x - y := by
      rw [show x + 2 * P - y = (x - y) + 2 * P by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [e, Nat.div_eq_of_lt (by omega)]

theorem noUnxor_rippleSteps : ∀ (K : ℕ) (rA rB : QRegister (K + 1) n) (ci : Wire n)
    (rC : QRegister K n), ∀ s ∈ rippleSteps K rA rB ci rC, s.NoUnxor := by
  intro K
  induction K with
  | zero =>
    intro rA rB ci rC s hs
    simp only [rippleSteps, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> trivial
  | succ K ih =>
    intro rA rB ci rC s hs
    simp only [rippleSteps, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with ((rfl | rfl | rfl | rfl) | hs) | (rfl | rfl | rfl | rfl)
    all_goals first | trivial | exact ih _ _ _ _ s hs


theorem andCount_inv_sum (ss : List (Step n)) :
    ((ss.reverse.map Step.inv).map Step.andCount).sum = (ss.map (Step.andCount ∘ Step.inv)).sum := by
  rw [List.map_map, List.map_reverse, List.sum_reverse]

theorem andCount_inv_rippleSteps_aux : ∀ (K : ℕ) (rA rB : QRegister (K + 1) n) (ci : Wire n)
    (rC : QRegister K n), ((rippleSteps K rA rB ci rC).map (Step.andCount ∘ Step.inv)).sum = K := by
  intro K
  induction K with
  | zero =>
    intro rA rB ci rC
    rfl
  | succ K ih =>
    intro rA rB ci rC
    rw [rippleSteps, List.map_append, List.map_append, List.sum_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp_apply,
      Step.inv, Step.andCount]
    omega

theorem andCount_inv_rippleSteps (K : ℕ) (rA rB : QRegister (K + 1) n) (ci : Wire n)
    (rC : QRegister K n) :
    (((rippleSteps K rA rB ci rC).reverse.map Step.inv).map Step.andCount).sum = K := by
  rw [andCount_inv_sum]
  exact andCount_inv_rippleSteps_aux K rA rB ci rC

/-! ### Register facts -/


theorem disj_slice {N M : ℕ} (rData : QRegister N n) (rAnc : QRegister M n)
    (h : rData.DisjointWires rAnc) (a b : ℕ) (ha : a + b ≤ N) (a' b' : ℕ) (ha' : a' + b' ≤ M) :
    (rData.slice a b ha).DisjointWires (rAnc.slice a' b' ha') :=
  (h.compose_left _).compose_right _

/-- A slice of one register is disjoint from a wire of a disjoint register. -/
theorem slice_disj_wire {N M : ℕ} (rData : QRegister N n) (rAnc : QRegister M n)
    (h : rData.DisjointWires rAnc) (a b : ℕ) (ha : a + b ≤ N) (j : Fin M) :
    (rData.slice a b ha).DisjointWires (QRegister.singleton (rAnc j)) :=
  QRegister.disjoint_iff.mpr fun i _ ↦ (h.compose_left (QRegister.block a b ha)).ne i j

/-- A wire outside a slice of its register is disjoint from the slice. -/
theorem wire_disj_slice {M : ℕ} (rAnc : QRegister M n) (j : Fin M) (a b : ℕ) (ha : a + b ≤ M)
    (hj : (j : ℕ) < a ∨ a + b ≤ j) :
    (QRegister.singleton (rAnc j)).DisjointWires (rAnc.slice a b ha) :=
  QRegister.disjoint_iff.mpr fun _ i e ↦ apply_not_mem_slice rAnc j a b ha hj ⟨i, e.symm⟩

theorem anc_ne {M : ℕ} (rAnc : QRegister M n) (i j : ℕ) (hi : i < M) (hj : j < M) (h : i ≠ j) :
    rAnc ⟨i, hi⟩ ≠ rAnc ⟨j, hj⟩ := fun e ↦ h (congrArg Fin.val (rAnc.wires.injective e))

theorem anc_not_mem_slice {N M : ℕ} (rData : QRegister N n) (rAnc : QRegister M n)
    (h : rData.DisjointWires rAnc) (a b : ℕ) (ha : a + b ≤ N) (j : Fin M) :
    rAnc j ∉ Set.range (rData.slice a b ha).wires :=
  fun ⟨i, hi⟩ ↦ (h.compose_left (QRegister.block a b ha)).ne i j hi

theorem not_mem_single {a w : Wire n} (h : a ≠ w) : a ∉ Set.range (QRegister.singleton w).wires :=
  fun ⟨_, hi⟩ ↦ h hi.symm

theorem disj_concat_left {k m p : ℕ} {r : QRegister k n} {s : QRegister m n}
    {h : r.DisjointWires s} {u : QRegister p n} (h1 : r.DisjointWires u)
    (h2 : s.DisjointWires u) : (r.concat s h).DisjointWires u := by
  rw [QRegister.disjoint_iff]
  intro i j
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i
  · rw [QRegister.concat_apply_left]
    exact h1.ne i j
  · rw [QRegister.concat_apply_right]
    exact h2.ne i j

theorem disj_concat_right {k m p : ℕ} {r : QRegister k n} {s : QRegister m n}
    {h : r.DisjointWires s} {u : QRegister p n} (h1 : u.DisjointWires r)
    (h2 : u.DisjointWires s) : u.DisjointWires (r.concat s h) :=
  QRegister.disjoint_comm.mp
    (disj_concat_left (QRegister.disjoint_comm.mp h1) (QRegister.disjoint_comm.mp h2))

theorem not_mem_concat {k m : ℕ} {r : QRegister k n} {s : QRegister m n} {h : r.DisjointWires s}
    {w : Wire n} (h1 : w ∉ Set.range r.wires) (h2 : w ∉ Set.range s.wires) :
    w ∉ Set.range (r.concat s h).wires := by
  rintro ⟨i, hi⟩
  revert hi
  refine Fin.addCases (fun i hi ↦ ?_) (fun i hi ↦ ?_) i
  · rw [QRegister.concat_apply_left] at hi
    exact h1 ⟨i, hi⟩
  · rw [QRegister.concat_apply_right] at hi
    exact h2 ⟨i, hi⟩

/-- The value read from a register extended by one wire. -/
theorem localIdx_concat_single {k : ℕ} (r : QRegister k n) (w : Wire n)
    (h : r.DisjointWires (QRegister.singleton w)) (β : BitAssignment n) :
    (localIdx (r.concat (QRegister.singleton w) h) β : ℕ) =
      (localIdx r β : ℕ) + 2 ^ k * (β w).val := by
  rw [localIdx_val, localIdx_val, Fin.sum_univ_add, Fin.sum_univ_one]
  simp only [QRegister.concat_apply_left, QRegister.concat_apply_right,
    QRegister.singleton_apply, Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero, add_zero]
  ring


/-- The core of the comparator on abstract registers: the inverse ripple, a `CNOT` of the top bit of
`B` onto `t`, then the ripple again, flips `t` by `[x < y]` and changes nothing else. -/
theorem runList_comparatorCore (K : ℕ) (rA rB : QRegister (K + 1) n) (rC : QRegister K n)
    (ci t : Wire n) (hAB : rA.DisjointWires rB) (hAC : rA.DisjointWires rC)
    (hBC : rB.DisjointWires rC) (hciA : ci ∉ Set.range rA.wires) (hciB : ci ∉ Set.range rB.wires)
    (hciC : ci ∉ Set.range rC.wires) (htA : t ∉ Set.range rA.wires)
    (htB : t ∉ Set.range rB.wires) (htC : t ∉ Set.range rC.wires) (htci : t ≠ ci)
    (β : BitAssignment n) (hclean : ∀ i, β (rC i) = 0) (hci : β ci = 0)
    (x y : ℕ) (hx : (localIdx rB β : ℕ) = x) (hy : (localIdx rA β : ℕ) = y)
    (hxl : x < 2 ^ K) (hyl : y < 2 ^ K) :
    runList ((rippleSteps K rA rB ci rC).reverse.map Step.inv ++
        [cnot (rB (Fin.last K)) t] ++ rippleSteps K rA rB ci rC) β =
      some (update β t (β t + if x < y then 1 else 0)) := by
  have hM2 : 2 ^ (K + 1) = 2 * 2 ^ K := by ring
  have hP : 0 < 2 ^ K := by positivity
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = (x + 2 * 2 ^ K - y) % (2 * 2 ^ K) := ⟨_, rfl⟩
  have hdlt : d < 2 ^ (K + 1) := by
    rw [hd, hM2]
    exact Nat.mod_lt _ (by positivity)
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀, β₀ = writeReg β rB (basisBits (K + 1) ⟨d, hdlt⟩) := ⟨_, rfl⟩
  have hβ₀A : localIdx rA β₀ = localIdx rA β := by
    rw [hβ₀]
    exact localIdx_writeReg_of_disjoint β rB rA (QRegister.disjoint_comm.mp hAB) _
  have hβ₀B : (localIdx rB β₀ : ℕ) = d := by
    rw [hβ₀, localIdx_writeReg, basisBitsEquiv_symm_basisBits]
  have hβ₀ci : β₀ ci = 0 := by
    rw [hβ₀, writeReg_apply_of_not_mem _ _ _ _ hciB]
    exact hci
  have hβ₀t : β₀ t = β t := by
    rw [hβ₀, writeReg_apply_of_not_mem _ _ _ _ htB]
  have hβ₀C : ∀ i, β₀ (rC i) = 0 := fun i ↦ by
    rw [hβ₀, writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hBC) i)]
    exact hclean i
  -- writing back the original value of `B` undoes the subtraction
  have key : ∀ (m : ℕ) (hm : m < 2 ^ (K + 1)), m = x →
      writeReg β₀ rB (basisBits (K + 1) ⟨m, hm⟩) = β := by
    intro m hm hmx
    have hF : (⟨m, hm⟩ : Fin (2 ^ (K + 1))) = localIdx rB β := Fin.ext (by
      show m = _
      rw [hmx, hx])
    rw [hF, hβ₀, writeReg_writeReg, basisBits_basisBitsEquiv_symm, writeReg_self]
  have hidx : ((localIdx rA β₀ : ℕ) + (localIdx rB β₀ : ℕ) + (β₀ ci).val) % 2 ^ (K + 1) = x := by
    rw [hβ₀A, hβ₀B, hβ₀ci, hy, ZMod.val_zero, add_zero, hM2, hd]
    exact sub_arith (2 ^ K) x y hxl hyl
  have hR0 : runList (rippleSteps K rA rB ci rC) β₀ = some β := by
    rw [runList_rippleSteps K rA rB ci rC hAB hAC hBC hciA hciB hciC β₀ hβ₀C]
    exact congrArg some (key _ (Nat.mod_lt _ (by positivity)) hidx)
  have hrev : runList ((rippleSteps K rA rB ci rC).reverse.map Step.inv) β = some β₀ :=
    runList_inv (noUnxor_rippleSteps K rA rB ci rC) hR0
  -- the borrow bit
  have hbit : d / 2 ^ K % 2 = if x < y then 1 else 0 := by
    rw [hd]
    exact borrow_arith (2 ^ K) x y hP hxl hyl
  have hflag : β₀ (rB (Fin.last K)) = if x < y then 1 else 0 := by
    rw [hβ₀, writeReg_apply_reg, basisBits_mk_apply, Fin.val_last, hbit]
    split_ifs <;> simp
  obtain ⟨w, hw⟩ : ∃ w, w = β₀ t + β₀ (rB (Fin.last K)) := ⟨_, rfl⟩
  have hw' : w = β t + if x < y then 1 else 0 := by rw [hw, hβ₀t, hflag]
  have hex : rB (Fin.last K) ≠ t := fun h ↦ htB ⟨Fin.last K, h⟩
  have hcn : runList [cnot (rB (Fin.last K)) t] β₀ = some (update β₀ t w) := by
    rw [hw]
    simp only [runList_cons, runList_nil, Step.run, ite_eq_left hex, Option.bind_some]
  have hβ₁C : ∀ i, update β₀ t w (rC i) = 0 := fun i ↦ by
    rw [update_of_ne (fun h ↦ htC ⟨i, h⟩)]
    exact hβ₀C i
  have hidx₁ : ((localIdx rA (update β₀ t w) : ℕ) + (localIdx rB (update β₀ t w) : ℕ) +
      (update β₀ t w ci).val) % 2 ^ (K + 1) = x := by
    rw [localIdx_update_of_not_mem rA β₀ htA, localIdx_update_of_not_mem rB β₀ htB,
      update_of_ne (Ne.symm htci)]
    exact hidx
  have hR1 := runList_rippleSteps K rA rB ci rC hAB hAC hBC hciA hciB hciC (update β₀ t w) hβ₁C
  rw [runList_append, runList_append, hrev, Option.bind_some, hcn, Option.bind_some, hR1]
  refine congrArg some ?_
  rw [← hw', writeReg_update_of_not_mem _ _ _ htB, key _ (Nat.mod_lt _ (by positivity)) hidx₁]



/-! ### Thresholds and masses

`cumW`, `thr` and their lemmas are this repository's `QuantumSolutions/BlockEncoding/PreparePauliLCU.lean`, lines 2667 to
2731 (without `pickF`). `mass j = C_{j+1} - C_j` is the number of the `2^(b+μ)` alias slots that
term `j` receives. -/

open Finset

/-- Weight of the first `j` terms. -/
def cumW {L : ℕ} (w : PrepareWeights L) (j : ℕ) : ℚ :=
  ∑ i ∈ univ.filter (fun i : Fin L ↦ i.val < j), w i

/-- Threshold `C_j = ⌊2^(b+μ) (w_0 + ⋯ + w_{j-1}) / λ⌋` on the `2^(b+μ)` slots. -/
def thr (b L μ : ℕ) (w : PrepareWeights L) (j : ℕ) : ℕ :=
  ⌊(2 : ℚ) ^ (b + μ) * cumW w j / prepareLambda w⌋₊

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


theorem cumW_of_le (j : ℕ) (h : L ≤ j) : cumW w j = prepareLambda w := by
  unfold cumW prepareLambda
  rw [Finset.filter_true_of_mem fun i _ ↦ lt_of_lt_of_le i.isLt h]

theorem thr_of_le (hsum : 0 < prepareLambda w) (j : ℕ) (h : L ≤ j) :
    thr b L μ w j = 2 ^ (b + μ) := by
  unfold thr
  rw [cumW_of_le w j h, mul_div_assoc, div_self hsum.ne', mul_one]
  exact_mod_cast Nat.floor_natCast (2 ^ (b + μ))

end Thr

/-- Number of alias slots of term `j`. -/
def mass (b L μ : ℕ) (w : PrepareWeights L) (j : ℕ) : ℕ :=
  thr b L μ w (j + 1) - thr b L μ w j

theorem mass_zero {b L μ : ℕ} (w : PrepareWeights L) (hsum : 0 < prepareLambda w) (j : ℕ)
    (h : L ≤ j) : mass b L μ w j = 0 := by
  unfold mass
  rw [thr_of_le w hsum j h, thr_of_le w hsum (j + 1) (by omega), Nat.sub_self]

theorem mass_sum {b L μ : ℕ} (w : PrepareWeights L) (hLb : L ≤ 2 ^ b) (hw : ∀ j, 0 ≤ w j)
    (hsum : 0 < prepareLambda w) :
    ∑ j ∈ range (2 ^ b), mass b L μ w j = 2 ^ b * 2 ^ μ := by
  unfold mass
  rw [Finset.sum_range_tsub (f := thr b L μ w) (fun _ _ h ↦ thr_mono w hw hsum h),
    thr_of_le w hsum _ hLb, thr_zero, Nat.sub_zero, pow_add]

/-- The mass of term `j` is within `1 / (2^μ L)` of `w_j / λ` (the lookup solution's `fibre_bound`, with the fibre
count replaced by the mass). -/
theorem mass_bound {b L μ : ℕ} (w : PrepareWeights L) (hLb : L ≤ 2 ^ b) (hw : ∀ j, 0 ≤ w j)
    (hsum : 0 < prepareLambda w) (j : ℕ) (hj : j < L) :
    |((mass b L μ w j : ℕ) : ℚ) / 2 ^ (b + μ) - w ⟨j, hj⟩ / prepareLambda w| ≤
      1 / (2 ^ μ * L) := by
  have hm : thr b L μ w j ≤ thr b L μ w (j + 1) := thr_mono w hw hsum (Nat.le_succ _)
  rw [mass, Nat.cast_sub hm]
  set x : ℚ := (2 : ℚ) ^ (b + μ) * cumW w j / prepareLambda w with hx
  set y : ℚ := (2 : ℚ) ^ (b + μ) * cumW w (j + 1) / prepareLambda w with hy
  have hxy : y - x = (2 : ℚ) ^ (b + μ) * (w ⟨j, hj⟩ / prepareLambda w) := by
    rw [hx, hy, cumW_succ w j hj]; field_simp; ring
  have hxnn : 0 ≤ x := by
    rw [hx]; have : 0 ≤ cumW w j := by
      rw [← cumW_zero w]; exact cumW_mono w hw (Nat.zero_le _)
    positivity
  have hynn : 0 ≤ y := by
    rw [hy]; have : 0 ≤ cumW w (j + 1) := by
      rw [← cumW_zero w]; exact cumW_mono w hw (Nat.zero_le _)
    positivity
  have hx1 := Nat.floor_le hxnn
  have hx2 := Nat.lt_floor_add_one x
  have hy1 := Nat.floor_le hynn
  have hy2 := Nat.lt_floor_add_one y
  have hxf : thr b L μ w j = ⌊x⌋₊ := rfl
  have hyf : thr b L μ w (j + 1) = ⌊y⌋₊ := rfl
  rw [hxf, hyf] at *
  have hpos : (0 : ℚ) < 2 ^ (b + μ) := by positivity
  have hd : |((⌊y⌋₊ : ℚ) - ⌊x⌋₊) / 2 ^ (b + μ) - w ⟨j, hj⟩ / prepareLambda w| ≤
      1 / 2 ^ (b + μ) := by
    have e : ((⌊y⌋₊ : ℚ) - ⌊x⌋₊) / 2 ^ (b + μ) - w ⟨j, hj⟩ / prepareLambda w =
        (((⌊y⌋₊ : ℚ) - ⌊x⌋₊) - (y - x)) / 2 ^ (b + μ) := by
      rw [hxy]; field_simp
    rw [e, abs_div, abs_of_pos hpos]
    refine div_le_div_of_nonneg_right ?_ hpos.le
    rw [abs_le]; constructor <;> linarith
  refine hd.trans ?_
  have hL : (1 : ℚ) ≤ L := by
    have : 1 ≤ L := by omega
    exact_mod_cast this
  have hLb' : (L : ℚ) ≤ 2 ^ b := by exact_mod_cast hLb
  rw [pow_add]
  refine one_div_le_one_div_of_le (by positivity) ?_
  nlinarith [pow_pos (show (0 : ℚ) < 2 by norm_num) μ]


/-! ### Bit-level semantics of the alias steps

The data register has `D = b + (b + 2 μ + 1)` wires: index `[0, b)`, uniform sample `σ`
`[b, b + μ)`, alternate index `[b + μ, 2 b + μ)`, keep value `[2 b + μ, 2 b + 2 μ)` and the flag
`2 b + 2 μ`. The three stages act on data bits by the involutions `F1` (table lookup of alternate
and keep), `F2` (flag `:= [σ ≥ keep]`) and `F3` (swap of index and alternate when the flag is
set). -/

/-- Number of data wires. -/
abbrev DD (b μ : ℕ) : ℕ := b + (b + 2 * μ + 1)

/-- Bit `k` of a bit assignment, `0` past the end. -/
def gv {D : ℕ} (γ : BitAssignment D) (k : ℕ) : ZMod 2 := if h : k < D then γ ⟨k, h⟩ else 0

theorem gv_fin {D : ℕ} (γ : BitAssignment D) (i : Fin D) : gv γ i.val = γ i := by
  simp [gv]

theorem gv_ge {D : ℕ} (γ : BitAssignment D) (k : ℕ) (h : D ≤ k) : gv γ k = 0 := by
  simp [gv, show ¬ k < D by omega]

/-- The `w`-bit number stored at wires `a, …, a + w - 1`, least significant first. -/
def rdv {D : ℕ} (γ : BitAssignment D) (a w : ℕ) : ℕ :=
  ∑ j ∈ Finset.range w, (gv γ (a + j)).val * 2 ^ j

theorem rdv_congr {D D' : ℕ} (γ : BitAssignment D) (γ' : BitAssignment D') (a w : ℕ)
    (h : ∀ j < w, gv γ (a + j) = gv γ' (a + j)) : rdv γ a w = rdv γ' a w :=
  Finset.sum_congr rfl fun j hj ↦ by rw [h j (Finset.mem_range.1 hj)]

theorem zmod2_val_le (x : ZMod 2) : x.val ≤ 1 := by
  have := ZMod.val_lt x
  omega

theorem rdv_lt {D : ℕ} (γ : BitAssignment D) (a w : ℕ) : rdv γ a w < 2 ^ w := by
  induction w with
  | zero => simp [rdv]
  | succ w ih =>
    rw [rdv, Finset.sum_range_succ, ← rdv, pow_succ]
    have := zmod2_val_le (gv γ (a + w))
    nlinarith

theorem natCast_bit_val (v j : ℕ) : (((v / 2 ^ j % 2 : ℕ) : ZMod 2)).val = v / 2 ^ j % 2 := by
  rw [ZMod.val_natCast, Nat.mod_mod]

theorem rdv_bits {D : ℕ} (γ : BitAssignment D) (a w v : ℕ)
    (h : ∀ j < w, gv γ (a + j) = ((v / 2 ^ j % 2 : ℕ) : ZMod 2)) : rdv γ a w = v % 2 ^ w := by
  induction w with
  | zero => simp [rdv, Nat.mod_one]
  | succ w ih =>
    rw [rdv, Finset.sum_range_succ, ← rdv, ih fun j hj ↦ h j (by omega), h w (by omega),
      natCast_bit_val, Nat.mod_pow_succ]
    ring

theorem rdv_bit {D : ℕ} (γ : BitAssignment D) (a w j : ℕ) (hj : j < w) :
    ((rdv γ a w / 2 ^ j % 2 : ℕ) : ZMod 2) = gv γ (a + j) := by
  induction w with
  | zero => omega
  | succ w ih =>
    have hlt := rdv_lt γ a w
    have hv := zmod2_val_le (gv γ (a + w))
    rw [rdv, Finset.sum_range_succ, ← rdv]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [← ih hj]
      congr 1
      have h2 : 2 ^ w = 2 ^ j * (2 * 2 ^ (w - j - 1)) := by
        rw [← pow_succ', ← pow_add]; congr 1; omega
      have e : rdv γ a w + (gv γ (a + w)).val * 2 ^ w =
          rdv γ a w + 2 ^ j * (2 * ((gv γ (a + w)).val * 2 ^ (w - j - 1))) := by
        rw [h2]; ring
      rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
    · rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add,
        Nat.mod_eq_of_lt (by omega)]
      exact ZMod.natCast_zmod_val _

section Stages

variable (b μ : ℕ)

/-- Stage 1: the lookup adds `f x` (alternate in the low `b` bits, keep above) to wires
`[b + μ, 2 b + 2 μ)`, where `x` is the index. -/
def F1 (f : ℕ → ℕ) (γ : BitAssignment (DD b μ)) : BitAssignment (DD b μ) := fun i ↦
  gv γ i.val + if b + μ ≤ i.val ∧ i.val < 2 * b + 2 * μ then
    ((f (rdv γ 0 b) / 2 ^ (i.val - (b + μ)) % 2 : ℕ) : ZMod 2) else 0

/-- Stage 2: the flag is flipped by `[σ < keep] + 1 = [σ ≥ keep]`. -/
def F2 (γ : BitAssignment (DD b μ)) : BitAssignment (DD b μ) := fun i ↦
  gv γ i.val + if i.val = 2 * b + 2 * μ then
    (if rdv γ b μ < rdv γ (2 * b + μ) μ then 1 else 0) + 1 else 0

/-- Stage 3: index and alternate are swapped when the flag is set. -/
def F3 (γ : BitAssignment (DD b μ)) : BitAssignment (DD b μ) := fun i ↦
  gv γ i.val + gv γ (2 * b + 2 * μ) *
    (if i.val < b then gv γ i.val + gv γ (b + μ + i.val)
     else if b + μ ≤ i.val ∧ i.val < 2 * b + μ then gv γ (i.val - (b + μ)) + gv γ i.val else 0)

theorem gv_F1 (f : ℕ → ℕ) (γ : BitAssignment (DD b μ)) (k : ℕ) :
    gv (F1 b μ f γ) k = gv γ k + if b + μ ≤ k ∧ k < 2 * b + 2 * μ then
      ((f (rdv γ 0 b) / 2 ^ (k - (b + μ)) % 2 : ℕ) : ZMod 2) else 0 := by
  have hD : DD b μ = b + (b + 2 * μ + 1) := rfl
  by_cases hk : k < DD b μ
  · simp only [gv, dif_pos hk, F1]
  · rw [gv_ge _ _ (by omega), gv_ge _ _ (by omega), if_neg (by omega), add_zero]

theorem gv_F2 (γ : BitAssignment (DD b μ)) (k : ℕ) :
    gv (F2 b μ γ) k = gv γ k + if k = 2 * b + 2 * μ then
      (if rdv γ b μ < rdv γ (2 * b + μ) μ then 1 else 0) + 1 else 0 := by
  have hD : DD b μ = b + (b + 2 * μ + 1) := rfl
  by_cases hk : k < DD b μ
  · simp only [gv, dif_pos hk, F2]
  · rw [gv_ge _ _ (by omega), gv_ge _ _ (by omega), if_neg (by omega), add_zero]

theorem gv_F3 (γ : BitAssignment (DD b μ)) (k : ℕ) :
    gv (F3 b μ γ) k = gv γ k + gv γ (2 * b + 2 * μ) *
      (if k < b then gv γ k + gv γ (b + μ + k)
       else if b + μ ≤ k ∧ k < 2 * b + μ then gv γ (k - (b + μ)) + gv γ k else 0) := by
  have hD : DD b μ = b + (b + 2 * μ + 1) := rfl
  by_cases hk : k < DD b μ
  · simp only [gv, dif_pos hk, F3]
  · rw [gv_ge _ _ (by omega), gv_ge _ _ (by omega), if_neg (by omega), if_neg (by omega),
      mul_zero, add_zero]

theorem zmod2_add_add (x y : ZMod 2) : x + y + y = x := by
  revert x y; decide

theorem F1_inv (f : ℕ → ℕ) (γ : BitAssignment (DD b μ)) : F1 b μ f (F1 b μ f γ) = γ := by
  have hr : rdv (F1 b μ f γ) 0 b = rdv γ 0 b :=
    rdv_congr _ _ _ _ fun j hj ↦ by rw [gv_F1, if_neg (by omega), add_zero]
  funext i
  rw [← gv_fin (F1 b μ f (F1 b μ f γ)), gv_F1, gv_F1, hr, zmod2_add_add, gv_fin]

theorem F2_inv (γ : BitAssignment (DD b μ)) : F2 b μ (F2 b μ γ) = γ := by
  have hr1 : rdv (F2 b μ γ) b μ = rdv γ b μ :=
    rdv_congr _ _ _ _ fun j hj ↦ by rw [gv_F2, if_neg (by omega), add_zero]
  have hr2 : rdv (F2 b μ γ) (2 * b + μ) μ = rdv γ (2 * b + μ) μ :=
    rdv_congr _ _ _ _ fun j hj ↦ by rw [gv_F2, if_neg (by omega), add_zero]
  funext i
  rw [← gv_fin (F2 b μ (F2 b μ γ)), gv_F2, gv_F2, hr1, hr2, zmod2_add_add, gv_fin]

theorem F3_inv (γ : BitAssignment (DD b μ)) : F3 b μ (F3 b μ γ) = γ := by
  have hf : gv (F3 b μ γ) (2 * b + 2 * μ) = gv γ (2 * b + 2 * μ) := by
    rw [gv_F3, if_neg (by omega), if_neg (by omega), mul_zero, add_zero]
  funext i
  rw [← gv_fin (F3 b μ (F3 b μ γ)), gv_F3, hf, ← gv_fin γ i]
  by_cases h1 : i.val < b
  · have a1 : ¬ b + μ + i.val < b := by omega
    have a2 : b + μ ≤ b + μ + i.val := by omega
    have a2' : b + μ + i.val < 2 * b + μ := by omega
    have a3 : b + μ + i.val - (b + μ) = i.val := by omega
    simp only [gv_F3, h1, a1, a2, a2', a3, ↓reduceIte, and_self]
    generalize gv γ i.val = x
    generalize gv γ (b + μ + i.val) = y
    generalize gv γ (2 * b + 2 * μ) = c
    revert x y c; decide
  · by_cases h2 : b + μ ≤ i.val ∧ i.val < 2 * b + μ
    · have a4 : i.val - (b + μ) < b := by omega
      have a5 : b + μ + (i.val - (b + μ)) = i.val := by omega
      simp only [gv_F3, h1, h2, a4, a5, ↓reduceIte, and_self]
      generalize gv γ i.val = x
      generalize gv γ (i.val - (b + μ)) = y
      generalize gv γ (2 * b + 2 * μ) = c
      revert x y c; decide
    · simp only [gv_F3, h1, h2, ↓reduceIte, mul_zero, add_zero]

/-- The basis permutation of the data bits performed by the three stages. -/
def Pbits (f : ℕ → ℕ) : Equiv.Perm (BitAssignment (DD b μ)) :=
  (Function.Involutive.toPerm _ (F1_inv b μ f)).trans
    ((Function.Involutive.toPerm _ (F2_inv b μ)).trans
      (Function.Involutive.toPerm _ (F3_inv b μ)))

theorem Pbits_apply (f : ℕ → ℕ) (γ : BitAssignment (DD b μ)) :
    Pbits b μ f γ = F3 b μ (F2 b μ (F1 b μ f γ)) := rfl

end Stages


/-! ### The step lists and their action on basis states -/

theorem localIdx_slice_rdv {D : ℕ} (r : QRegister D n) (a w : ℕ) (h : a + w ≤ D)
    (β : BitAssignment n) :
    (localIdx (r.slice a w h) β : ℕ) = rdv (fun i ↦ β (r i)) a w := by
  rw [localIdx_val, rdv,
    ← Fin.sum_univ_eq_sum_range (fun j ↦ (gv (fun i ↦ β (r i)) (a + j)).val * 2 ^ j)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [gv, dif_pos (by have := j.isLt; omega)]
  rfl

theorem gv_rd {D : ℕ} (r : QRegister D n) (β : BitAssignment n) (k : ℕ) (h : k < D) :
    gv (fun i ↦ β (r i)) k = β (r ⟨k, h⟩) := by
  simp [gv, h]

theorem slice_at {D : ℕ} (r : QRegister D n) (a w : ℕ) (h : a + w ≤ D) (j : Fin w) (k : Fin D)
    (hk : k.val = a + j.val) : (r.slice a w h) j = r k := by
  rw [QRegister.slice_apply]
  exact congrArg r (Fin.ext hk.symm)

theorem eq_writeReg_of {k : ℕ} (β β' : BitAssignment n) (r : QRegister k n) (X : BitAssignment k)
    (hon : ∀ i, β' (r i) = X i) (hoff : ∀ w ∉ Set.range r.wires, β' w = β w) :
    β' = writeReg β r X := by
  calc β' = writeReg β r (fun i ↦ β' (r i)) := (writeReg_eq_of_eqOn β β' r hoff).symm
    _ = writeReg β r X := by
      congr 1
      funext i
      exact hon i

theorem rd_writeReg {k : ℕ} (β : BitAssignment n) (r : QRegister k n) (X : BitAssignment k) :
    (fun i ↦ writeReg β r X (r i)) = X := by
  funext i
  exact writeReg_apply_reg _ _ _ _

section Program

variable (b μ : ℕ) {A : ℕ} (rData : QRegister (DD b μ) n) (rAnc : QRegister A n)

/-- Keep value register, extended by the clean ancilla `rAnc 1` as its top bit. -/
def regKeep (hAμ : μ + 3 ≤ A) (hd : rData.DisjointWires rAnc) : QRegister (μ + 1) n :=
  (rData.slice (2 * b + μ) μ (by unfold DD; omega)).concat
    (QRegister.singleton (rAnc ⟨1, by omega⟩)) (slice_disj_wire rData rAnc hd _ _ _ _)

/-- Uniform sample register, extended by the clean ancilla `rAnc 0` as its top bit. -/
def regSig (hAμ : μ + 3 ≤ A) (hd : rData.DisjointWires rAnc) : QRegister (μ + 1) n :=
  (rData.slice b μ (by unfold DD; omega)).concat
    (QRegister.singleton (rAnc ⟨0, by omega⟩)) (slice_disj_wire rData rAnc hd _ _ _ _)

/-- Stage 1: unary-iteration table lookup of `f x` into alternate and keep. -/
def stepsS1 (f : ℕ → ℕ) (hAb : b ≤ A) : List (Step n) :=
  lookupSteps (b + μ) (rData.slice (b + μ) (b + μ) (by unfold DD; omega)) b none
    (rData.slice 0 b (by unfold DD; omega)) (rAnc.slice 0 b (by omega)) (tableBits (b + μ) f)

/-- Stage 2: comparator `flag ^= [σ < keep]`, then `X` on the flag. -/
def stepsS2 (hAμ : μ + 3 ≤ A) (hd : rData.DisjointWires rAnc) : List (Step n) :=
  (rippleSteps μ (regKeep b μ rData rAnc hAμ hd) (regSig b μ rData rAnc hAμ hd)
      (rAnc ⟨2, by omega⟩) (rAnc.slice 3 μ (by omega))).reverse.map Step.inv ++
    [cnot ((regSig b μ rData rAnc hAμ hd) (Fin.last μ))
      (rData ⟨2 * b + 2 * μ, by unfold DD; omega⟩)] ++
    rippleSteps μ (regKeep b μ rData rAnc hAμ hd) (regSig b μ rData rAnc hAμ hd)
      (rAnc ⟨2, by omega⟩) (rAnc.slice 3 μ (by omega)) ++
    [Step.x (rData ⟨2 * b + 2 * μ, by unfold DD; omega⟩)]

/-- Stage 3: controlled swap of index and alternate, controlled by the flag. -/
def stepsS3 (hAμ : μ + 3 ≤ A) : List (Step n) :=
  cswapSteps (rData ⟨2 * b + 2 * μ, by unfold DD; omega⟩) (rAnc ⟨0, by omega⟩) b
    (rData.slice 0 b (by unfold DD; omega)) (rData.slice (b + μ) b (by unfold DD; omega))

/-- All steps of the alias `PREPARE` after the Hadamards. -/
def aliasSteps (f : ℕ → ℕ) (hAb : b ≤ A) (hAμ : μ + 3 ≤ A) (hd : rData.DisjointWires rAnc) :
    List (Step n) :=
  stepsS1 b μ rData rAnc f hAb ++ stepsS2 b μ rData rAnc hAμ hd ++ stepsS3 b μ rData rAnc hAμ

variable {b μ rData rAnc}

theorem run_S1 (f : ℕ → ℕ) (hAb : b ≤ A) (hd : rData.DisjointWires rAnc) (β : BitAssignment n)
    (hcl : ∀ j, β (rAnc j) = 0) :
    runList (stepsS1 b μ rData rAnc f hAb) β =
      some (writeReg β rData (F1 b μ f (fun i ↦ β (rData i)))) := by
  have hD : DD b μ = b + (b + 2 * μ + 1) := rfl
  have hY : b + μ + (b + μ) ≤ DD b μ := by omega
  have hX : 0 + b ≤ DD b μ := by omega
  rw [stepsS1, runList_lookupSteps (b + μ) _ b none _ _ _
    (disj_slice rData rAnc hd 0 b hX 0 b (by omega))
    (QRegister.slice_disjoint_of_le rData 0 b (b + μ) (b + μ) hX hY (by omega))
    (QRegister.disjoint_comm.mp (disj_slice rData rAnc hd _ _ hY 0 b (by omega)))
    (fun _ ↦ ctrlNe_none _) (fun _ ↦ ctrlNe_none _) (fun _ ↦ ctrlNe_none _) β (fun _ ↦ hcl _)]
  congr 1
  refine eq_writeReg_of _ _ _ _ (fun i ↦ ?_) (fun w hw ↦ ?_)
  · by_cases hi : b + μ ≤ i.val ∧ i.val < 2 * b + 2 * μ
    · have e : rData i = (rData.slice (b + μ) (b + μ) hY) ⟨i.val - (b + μ), by omega⟩ :=
        (slice_at rData _ _ hY _ i (by show i.val = b + μ + (i.val - (b + μ)); omega)).symm
      rw [e, writeReg_apply_reg, ← e]
      simp only [F1, gv_fin, hi.1, hi.2, and_self, ↓reduceIte, ctrlVal, one_mul, tableBits,
        localIdx_slice_rdv, Fin.val_mk]
    · rw [writeReg_apply_of_not_mem _ _ _ _
        (apply_not_mem_slice rData i (b + μ) (b + μ) hY (by omega))]
      simp only [F1, gv_fin, hi, ↓reduceIte, add_zero]
  · exact writeReg_apply_of_not_mem _ _ _ _ (not_mem_slice hw _ _ _)

theorem run_S2 (hAμ : μ + 3 ≤ A) (hd : rData.DisjointWires rAnc) (β : BitAssignment n)
    (hcl : ∀ j, β (rAnc j) = 0) :
    runList (stepsS2 b μ rData rAnc hAμ hd) β =
      some (writeReg β rData (F2 b μ (fun i ↦ β (rData i)))) := by
  have hD : DD b μ = b + (b + 2 * μ + 1) := rfl
  have hK : 2 * b + μ + μ ≤ DD b μ := by omega
  have hS : b + μ ≤ DD b μ := by omega
  have hC : 3 + μ ≤ A := by omega
  have hfl : 2 * b + 2 * μ < DD b μ := by omega
  have h0 : 0 < A := by omega
  have h1 : 1 < A := by omega
  have h2 : 2 < A := by omega
  set t := rData ⟨2 * b + 2 * μ, hfl⟩ with ht
  have hss : (rData.slice b μ hS).DisjointWires (rData.slice (2 * b + μ) μ hK) :=
    QRegister.slice_disjoint_of_le rData b μ (2 * b + μ) μ hS hK (by omega)
  have s10 : (QRegister.singleton (rAnc ⟨1, h1⟩)).DisjointWires
      (QRegister.singleton (rAnc ⟨0, h0⟩)) :=
    QRegister.disjoint_iff.mpr fun _ _ ↦ anc_ne rAnc 1 0 h1 h0 (by omega)
  have hAB : (regKeep b μ rData rAnc hAμ hd).DisjointWires (regSig b μ rData rAnc hAμ hd) :=
    disj_concat_left
      (disj_concat_right (QRegister.disjoint_comm.mp hss) (slice_disj_wire rData rAnc hd _ _ _ _))
      (disj_concat_right (QRegister.disjoint_comm.mp (slice_disj_wire rData rAnc hd _ _ _ _)) s10)
  have hAC : (regKeep b μ rData rAnc hAμ hd).DisjointWires (rAnc.slice 3 μ hC) :=
    disj_concat_left (disj_slice rData rAnc hd _ _ _ _ _ _)
      (wire_disj_slice rAnc ⟨1, h1⟩ 3 μ hC (Or.inl (by show 1 < 3; omega)))
  have hBC : (regSig b μ rData rAnc hAμ hd).DisjointWires (rAnc.slice 3 μ hC) :=
    disj_concat_left (disj_slice rData rAnc hd _ _ _ _ _ _)
      (wire_disj_slice rAnc ⟨0, h0⟩ 3 μ hC (Or.inl (by show 0 < 3; omega)))
  have hciA : rAnc ⟨2, h2⟩ ∉ Set.range (regKeep b μ rData rAnc hAμ hd).wires :=
    not_mem_concat (anc_not_mem_slice rData rAnc hd _ _ _ _)
      (not_mem_single (anc_ne rAnc 2 1 h2 h1 (by omega)))
  have hciB : rAnc ⟨2, h2⟩ ∉ Set.range (regSig b μ rData rAnc hAμ hd).wires :=
    not_mem_concat (anc_not_mem_slice rData rAnc hd _ _ _ _)
      (not_mem_single (anc_ne rAnc 2 0 h2 h0 (by omega)))
  have hciC : rAnc ⟨2, h2⟩ ∉ Set.range (rAnc.slice 3 μ hC).wires :=
    apply_not_mem_slice rAnc ⟨2, h2⟩ 3 μ hC (Or.inl (by show 2 < 3; omega))
  have htA : t ∉ Set.range (regKeep b μ rData rAnc hAμ hd).wires :=
    not_mem_concat (apply_not_mem_slice rData _ (2 * b + μ) μ hK
      (Or.inr (by show 2 * b + μ + μ ≤ 2 * b + 2 * μ; omega))) (not_mem_single (hd.ne _ _))
  have htB : t ∉ Set.range (regSig b μ rData rAnc hAμ hd).wires :=
    not_mem_concat (apply_not_mem_slice rData _ b μ hS
      (Or.inr (by show b + μ ≤ 2 * b + 2 * μ; omega))) (not_mem_single (hd.ne _ _))
  have htC : t ∉ Set.range (rAnc.slice 3 μ hC).wires := fun ⟨j, hj⟩ ↦
    hd.ne ⟨2 * b + 2 * μ, hfl⟩ ⟨3 + j.val, by omega⟩
      (hj.symm.trans (QRegister.slice_apply rAnc 3 μ hC j))
  have htci : t ≠ rAnc ⟨2, h2⟩ := hd.ne _ _
  have hx : (localIdx (regSig b μ rData rAnc hAμ hd) β : ℕ) = rdv (fun i ↦ β (rData i)) b μ := by
    rw [regSig, localIdx_concat_single, localIdx_slice_rdv, hcl, ZMod.val_zero, mul_zero,
      add_zero]
  have hy : (localIdx (regKeep b μ rData rAnc hAμ hd) β : ℕ) =
      rdv (fun i ↦ β (rData i)) (2 * b + μ) μ := by
    rw [regKeep, localIdx_concat_single, localIdx_slice_rdv, hcl, ZMod.val_zero, mul_zero,
      add_zero]
  rw [stepsS2, runList_append, runList_comparatorCore μ _ _ _ _ _ hAB hAC hBC hciA hciB hciC
    htA htB htC htci β (fun _ ↦ hcl _) (hcl _) _ _ hx hy (rdv_lt _ _ _) (rdv_lt _ _ _)]
  simp only [Option.bind_some, runList_cons, Step.run, runList_nil]
  rw [Function.update_self, Function.update_idem]
  congr 1
  rw [writeReg_eq_update β rData _ ⟨2 * b + 2 * μ, hfl⟩ (fun i hi ↦ ?_)]
  · simp only [F2, ↓reduceIte]
    rw [gv_rd rData β _ hfl, ← ht, add_assoc]
  · have : i.val ≠ 2 * b + 2 * μ := fun h ↦ hi (Fin.ext h)
    simp only [F2, gv_fin, this, ↓reduceIte, add_zero]

theorem run_S3 (hAμ : μ + 3 ≤ A) (hd : rData.DisjointWires rAnc) (β : BitAssignment n)
    (hcl : ∀ j, β (rAnc j) = 0) :
    runList (stepsS3 b μ rData rAnc hAμ) β =
      some (writeReg β rData (F3 b μ (fun i ↦ β (rData i)))) := by
  have hD : DD b μ = b + (b + 2 * μ + 1) := rfl
  have hI : 0 + b ≤ DD b μ := by omega
  have hL : b + μ + b ≤ DD b μ := by omega
  have hfl : 2 * b + 2 * μ < DD b μ := by omega
  have h0 : 0 < A := by omega
  obtain ⟨β', hrun, hoff, hA, hB⟩ := runList_cswapSteps (rData ⟨2 * b + 2 * μ, hfl⟩)
    (rAnc ⟨0, h0⟩) b (rData.slice 0 b hI) (rData.slice (b + μ) b hL)
    (QRegister.slice_disjoint_of_le rData 0 b (b + μ) b hI hL (by omega))
    (apply_not_mem_slice rData _ 0 b hI (Or.inr (by show 0 + b ≤ 2 * b + 2 * μ; omega)))
    (apply_not_mem_slice rData _ (b + μ) b hL (Or.inr (by show b + μ + b ≤ 2 * b + 2 * μ; omega)))
    (hd.ne _ _) (anc_not_mem_slice rData rAnc hd _ _ _ _) (anc_not_mem_slice rData rAnc hd _ _ _ _)
    β (hcl _)
  rw [stepsS3, hrun]
  congr 1
  refine eq_writeReg_of _ _ _ _ (fun i ↦ ?_) (fun w hw ↦ hoff w (not_mem_slice hw _ _ _)
    (not_mem_slice hw _ _ _))
  by_cases h1 : i.val < b
  · have e : rData i = (rData.slice 0 b hI) ⟨i.val, h1⟩ :=
      (slice_at rData _ _ hI _ i (by show i.val = 0 + i.val; omega)).symm
    rw [e, hA, ← e, slice_at rData (b + μ) b hL ⟨i.val, h1⟩ ⟨b + μ + i.val, by omega⟩ rfl]
    simp only [F3, gv_fin, h1, ↓reduceIte]
    rw [gv_rd rData β _ hfl, gv_rd rData β (b + μ + i.val) (by omega)]
  · by_cases h2 : b + μ ≤ i.val ∧ i.val < 2 * b + μ
    · have e : rData i = (rData.slice (b + μ) b hL) ⟨i.val - (b + μ), by omega⟩ :=
        (slice_at rData _ _ hL _ i (by show i.val = b + μ + (i.val - (b + μ)); omega)).symm
      rw [e, hB, ← e, slice_at rData 0 b hI ⟨i.val - (b + μ), by omega⟩
        ⟨i.val - (b + μ), by omega⟩ (by show i.val - (b + μ) = 0 + (i.val - (b + μ)); omega)]
      simp only [F3, gv_fin, h1, h2, and_self, ↓reduceIte]
      rw [gv_rd rData β _ hfl, gv_rd rData β (i.val - (b + μ)) (by omega)]
    · rw [hoff _ (apply_not_mem_slice rData i 0 b hI (by omega))
        (apply_not_mem_slice rData i (b + μ) b hL (by omega))]
      simp only [F3, gv_fin, h1, h2, ↓reduceIte, mul_zero, add_zero]

theorem run_aliasSteps (f : ℕ → ℕ) (hAb : b ≤ A) (hAμ : μ + 3 ≤ A)
    (hd : rData.DisjointWires rAnc) (β : BitAssignment n) (hcl : ∀ j, β (rAnc j) = 0) :
    runList (aliasSteps b μ rData rAnc f hAb hAμ hd) β =
      some (writeReg β rData (Pbits b μ f (fun i ↦ β (rData i)))) := by
  have hcl' : ∀ X : BitAssignment (DD b μ), ∀ j, writeReg β rData X (rAnc j) = 0 := fun X j ↦ by
    rw [writeReg_apply_of_not_mem _ _ _ _ (fun ⟨i, hi⟩ ↦ hd.ne i j hi)]
    exact hcl j
  rw [aliasSteps, runList_append, runList_append, run_S1 f hAb hd β hcl, Option.bind_some,
    run_S2 hAμ hd _ (hcl' _), Option.bind_some, writeReg_writeReg, run_S3 hAμ hd _ (hcl' _)]
  simp only [rd_writeReg, writeReg_writeReg, Pbits_apply]

end Program


/-! ### Hadamards on the first `t` data wires -/

open Finset Operator Matrix

/-- Hadamards on the first `t` of `D` wires. -/
def hAll (D t : ℕ) (ht : t ≤ D) : Circuit D :=
  Circuit.sequence (List.ofFn fun i : Fin t ↦ Circuit.H (⟨i.val, by omega⟩ : Fin D))

/-- The bit assignment equal to `γ` on the first `t` wires and zero elsewhere. -/
def extZ (D t : ℕ) (γ : Fin t → ZMod 2) : BitAssignment D := fun i ↦
  if h : i.val < t then γ ⟨i.val, h⟩ else 0

theorem hAll_succ (D t : ℕ) (ht : t + 1 ≤ D) :
    (hAll D (t + 1) ht).eval =
      (Circuit.H (⟨t, by omega⟩ : Fin D)).eval * (hAll D t (by omega)).eval := by
  unfold hAll
  rw [Circuit.eval_sequence, Circuit.eval_sequence, List.ofFn_succ', List.concat_eq_append,
    List.map_append, List.reverse_append]
  simp [Fin.val_last]

theorem extZ_snoc (D t : ℕ) (ht : t + 1 ≤ D) (γ : Fin t → ZMod 2) (a : ZMod 2) :
    extZ D (t + 1) (Fin.snoc γ a) = Function.update (extZ D t γ) (⟨t, by omega⟩ : Fin D) a := by
  funext i
  by_cases hi : i = (⟨t, by omega⟩ : Fin D)
  · subst hi
    rw [Function.update_self]
    have key : ∀ h : t < t + 1, (Fin.snoc γ a : Fin (t + 1) → ZMod 2) ⟨t, h⟩ = a := by
      intro h
      have : (⟨t, h⟩ : Fin (t + 1)) = Fin.last t := Fin.ext (by simp)
      rw [this, Fin.snoc_last]
    unfold extZ
    rw [dif_pos (by simp)]
    exact key _
  · rw [Function.update_of_ne hi]
    have hi' : i.val ≠ t := fun h ↦ hi (Fin.ext h)
    unfold extZ
    by_cases h1 : i.val < t
    · rw [dif_pos h1, dif_pos (by omega)]
      have : (⟨i.val, by omega⟩ : Fin (t + 1)) = Fin.castSucc ⟨i.val, h1⟩ := Fin.ext rfl
      rw [this, Fin.snoc_castSucc]
    · rw [dif_neg h1, dif_neg (by omega)]

theorem extZ_wire_zero (D t : ℕ) (ht : t + 1 ≤ D) (γ : Fin t → ZMod 2) :
    extZ D t γ (⟨t, by omega⟩ : Fin D) = 0 := by
  simp [extZ]

theorem sum_zmod2 {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) : ∑ a, f a = f 0 + f 1 :=
  Fin.sum_univ_two f

theorem mulVec_mul_unitary {d : ℕ} (A B : Unitary d) (v : Fin d → ℂ) :
    (A * B).1.mulVec v = A.1.mulVec (B.1.mulVec v) := by
  rw [Matrix.mulVec_mulVec]; rfl

theorem hAll_ket (D : ℕ) : ∀ (t : ℕ) (ht : t ≤ D),
    (hAll D t ht).eval.1.mulVec (ket (0 : BitAssignment D)) =
      ((Real.sqrt (1 / 2) : ℂ) ^ t) • ∑ γ : Fin t → ZMod 2, ket (extZ D t γ) := by
  intro t
  induction t with
  | zero =>
    intro ht
    have h0 : (hAll D 0 ht).eval = 1 := by simp [hAll]
    have hz : ∀ γ : Fin 0 → ZMod 2, extZ D 0 γ = 0 := by
      intro γ; funext i; simp [extZ]
    rw [h0]
    simp only [hz, Finset.univ_unique, Finset.sum_singleton, pow_zero, one_smul]
    exact Matrix.one_mulVec _
  | succ t ih =>
    intro ht
    rw [hAll_succ, mulVec_mul_unitary, ih (by omega), Matrix.mulVec_smul, Matrix.mulVec_sum]
    have hstep : ∀ γ : Fin t → ZMod 2,
        (Circuit.H (⟨t, by omega⟩ : Fin D)).eval.1.mulVec (ket (extZ D t γ)) =
        (Real.sqrt (1 / 2) : ℂ) • ∑ a : ZMod 2, ket (extZ D (t + 1) (Fin.snoc γ a)) := by
      intro γ
      rw [ket_H, extZ_wire_zero D t ht γ]
      simp only [extZ_snoc D t ht, sum_zmod2]
      simp [bitSign]
    simp only [hstep]
    have hsplit : ∑ γ' : Fin (t + 1) → ZMod 2, ket (extZ D (t + 1) γ') =
        ∑ γ : Fin t → ZMod 2, ∑ a : ZMod 2, ket (extZ D (t + 1) (Fin.snoc γ a)) := by
      rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (t + 1) ↦ ZMod 2))
        (fun p ↦ ket (extZ D (t + 1) (Fin.snoc p.2 p.1)))
        (fun γ' ↦ ket (extZ D (t + 1) γ')) (fun p ↦ rfl)]
      exact Fintype.sum_prod_type_right _
    rw [hsplit, ← Finset.smul_sum, smul_smul, pow_succ]

theorem count_hAll (D t : ℕ) (ht : t ≤ D) {a : ℕ} (p : PrimitiveGate a)
    (hp : (⟨1, PrimitiveGate.H⟩ : Σ b, PrimitiveGate b) ≠ ⟨a, p⟩) :
    (hAll D t ht).count p = 0 := by
  unfold hAll
  rw [Circuit.count_sequence, List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_eq_zero fun i _ ↦ Circuit.count_gate_of_ne _ _ _ hp

/-! ### The realized unitary -/

/-- The basis permutation of the data register performed by the steps. -/
def sigP (b μ : ℕ) (f : ℕ → ℕ) : Equiv.Perm (Fin (2 ^ DD b μ)) :=
  ((basisBits (DD b μ)).trans (Pbits b μ f)).trans (basisBits (DD b μ)).symm

theorem clean_of_localIdx {m : ℕ} (r : QRegister m n) (β : BitAssignment n)
    (h : localIdx r β = 0) (j : Fin m) : β (r j) = 0 := by
  have := congrArg (basisBits m) h
  simp only [localIdx, Equiv.apply_symm_apply, basisBits_zero] at this
  exact congrFun this j

theorem realizes_alias {Var : Type} [DecidableEq Var] (v : Var) (b μ : ℕ) (f : ℕ → ℕ) {A : ℕ}
    (rData : QRegister (DD b μ) n) (rAnc : QRegister A n) (hAb : b ≤ A) (hAμ : μ + 3 ≤ A)
    (hd : rData.DisjointWires rAnc) (hbμ : b + μ ≤ DD b μ) :
    RealizesCleanSubroutine rData rAnc hd
      (permutationUnitary (sigP b μ f) * (hAll (DD b μ) (b + μ) hbμ).eval)
      (DynamicCircuit.seq (.circuit ((hAll (DD b μ) (b + μ) hbμ).onRegister rData))
        (compileList v (aliasSteps b μ rData rAnc f hAb hAμ hd))).compile := by
  obtain ⟨R, hK, hR, -⟩ := exists_lowerKraus_compileList v (aliasSteps b μ rData rAnc f hAb hAμ hd)
  refine CleanSubroutineBridge.realizesCleanSubroutine_of_lowerKraus_ket rData rAnc hd _
    ((lowerKraus_circuit _).qSeq hK) (fun β h0 ↦ ?_)
  rw [Circuit.eval_onRegister, QRegister.embedUnitary_mul, mulVec_mul_unitary,
    ← Matrix.mulVec_mulVec]
  set Q0 := rAnc.basisOutcomeProjector 0 with hQ
  set EP := (rData.embedUnitary (permutationUnitary (sigP b μ f))).1 with hEP
  set EH := (rData.embedUnitary (hAll (DD b μ) (b + μ) hbμ).eval).1 with hEH
  have hE : ∀ γ, EP.mulVec (ket γ) =
      ket (writeReg γ rData (basisBits _ (sigP b μ f (localIdx rData γ)))) := fun γ ↦ by
    have h := embedMatrix_permMatrix_mulVec_ket rData (sigP b μ f)⁻¹ γ
    rw [Equiv.Perm.inv_def, Equiv.symm_symm] at h
    rw [hEP, QRegister.embedUnitary_val]
    exact h
  have hkey : R * Q0 = EP * Q0 := by
    apply matrix_ext_ket
    intro γ
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQ, basisOutcomeProjector_mulVec_ket]
    by_cases hγ : localIdx rAnc γ = 0
    · rw [ite_eq_left hγ, hE, hR γ _ (run_aliasSteps f hAb hAμ hd γ (clean_of_localIdx rAnc γ hγ))]
      congr 2
      simp [sigP, localIdx]
    · rw [ite_eq_right hγ, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hk : Q0.mulVec (ket β) = ket β := by
    rw [hQ, basisOutcomeProjector_mulVec_ket, ite_eq_left h0]
  have hv : Q0.mulVec (EH.mulVec (ket β)) = EH.mulVec (ket β) := by
    rw [Matrix.mulVec_mulVec, hEH, CleanSubroutineBridge.embed_comm_proj rData rAnc hd,
      ← Matrix.mulVec_mulVec, hk]
  calc R.mulVec (EH.mulVec (ket β)) = R.mulVec (Q0.mulVec (EH.mulVec (ket β))) := by rw [hv]
    _ = (R * Q0).mulVec (EH.mulVec (ket β)) := by rw [Matrix.mulVec_mulVec]
    _ = (EP * Q0).mulVec (EH.mulVec (ket β)) := by rw [hkey]
    _ = EP.mulVec (EH.mulVec (ket β)) := by rw [← Matrix.mulVec_mulVec, hv]

/-! ### The index after the steps -/

section Index

variable (b μ : ℕ)

theorem zmod2_flip (x y : ZMod 2) : x + 1 * (x + y) = y := by
  revert x y; decide

theorem zmod2_noflip (x y : ZMod 2) : x + (0 + ((1 : ZMod 2) + 1)) * (x + y) = x := by
  revert x y; decide

theorem zmod2_flip' (x y : ZMod 2) : x + (0 + ((0 : ZMod 2) + 1)) * (x + y) = y := by
  revert x y; decide

theorem bit_low (a K b j : ℕ) (hj : j < b) :
    (a + 2 ^ b * K) / 2 ^ j % 2 = a / 2 ^ j % 2 := by
  have h2 : 2 ^ b = 2 ^ j * (2 * 2 ^ (b - j - 1)) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  rw [h2, mul_assoc, Nat.add_mul_div_left _ _ (by positivity), mul_assoc 2,
    Nat.add_mul_mod_self_left]

theorem bit_high (a K b j : ℕ) (ha : a < 2 ^ b) :
    (a + 2 ^ b * K) / 2 ^ (b + j) % 2 = K / 2 ^ j % 2 := by
  rw [pow_add, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt ha, zero_add]

/-- After the three stages, the index register holds `x` if `σ < K_x`, else the alternate
`a_x`, where the lookup returns `a_x + 2^b K_x` and all wires from `b + μ` on start at zero. -/
theorem rdv_Pbits (f : ℕ → ℕ) (γ : BitAssignment (DD b μ))
    (hz : ∀ k, b + μ ≤ k → gv γ k = 0) (a K : ℕ) (ha : a < 2 ^ b) (hK : K < 2 ^ μ)
    (hf : f (rdv γ 0 b) = a + 2 ^ b * K) :
    rdv (Pbits b μ f γ) 0 b = if rdv γ b μ < K then rdv γ 0 b else a := by
  have hs : rdv (F1 b μ f γ) b μ = rdv γ b μ :=
    rdv_congr _ _ _ _ fun j hj ↦ by rw [gv_F1, if_neg (by omega), add_zero]
  have hKr : rdv (F1 b μ f γ) (2 * b + μ) μ = K := by
    rw [rdv_bits _ _ _ K (fun j hj ↦ ?_), Nat.mod_eq_of_lt hK]
    rw [gv_F1, if_pos (by omega), hz _ (by omega), zero_add, hf,
      show 2 * b + μ + j - (b + μ) = b + j by omega, bit_high _ _ _ _ ha]
  have hflag : gv (F2 b μ (F1 b μ f γ)) (2 * b + 2 * μ) =
      0 + ((if rdv γ b μ < K then 1 else 0) + 1) := by
    rw [gv_F2, if_pos rfl, gv_F1, if_neg (by omega), add_zero, hz _ (by omega), hs, hKr]
  have hv : (if rdv γ b μ < K then rdv γ 0 b else a) < 2 ^ b := by
    split_ifs
    · exact rdv_lt _ _ _
    · exact ha
  rw [rdv_bits _ _ _ (if rdv γ b μ < K then rdv γ 0 b else a) (fun j hj ↦ ?_),
    Nat.mod_eq_of_lt hv]
  rw [Nat.zero_add]
  rw [Pbits_apply, gv_F3, hflag, if_pos hj, gv_F2, if_neg (show j ≠ 2 * b + 2 * μ by omega),
    add_zero, gv_F2, if_neg (show b + μ + j ≠ 2 * b + 2 * μ by omega), add_zero, gv_F1,
    if_neg (show ¬ (b + μ ≤ j ∧ j < 2 * b + 2 * μ) by omega), add_zero, gv_F1,
    if_pos (show b + μ ≤ b + μ + j ∧ b + μ + j < 2 * b + 2 * μ by omega),
    hz _ (show b + μ ≤ b + μ + j by omega), hf, show b + μ + j - (b + μ) = j by omega,
    bit_low _ _ _ _ hj]
  by_cases hc : rdv γ b μ < K
  · simp only [hc, ↓reduceIte]
    rw [rdv_bit γ 0 b j hj, Nat.zero_add]
    generalize gv γ j = x
    generalize (((a / 2 ^ j % 2 : ℕ) : ZMod 2)) = y
    revert x y; decide
  · simp only [hc, ↓reduceIte]
    generalize gv γ j = x
    generalize (((a / 2 ^ j % 2 : ℕ) : ZMod 2)) = y
    revert x y; decide

end Index

/-! ### Index probabilities of a uniform superposition of distinct basis states -/

theorem prob_inj (b g t : ℕ) (G : Fin (2 ^ t) → Fin (2 ^ (b + g))) (hG : Function.Injective G)
    (J : Fin (2 ^ t) → ℕ) (hJ : ∀ v, (G v).val % 2 ^ b = J v) (j : Fin (2 ^ b)) :
    prepareIndexProb b g (((Real.sqrt (1 / 2) : ℂ) ^ t) • ∑ v, basisState (G v)) j =
      ((univ.filter (fun v ↦ J v = j.val)).card : ℝ) / 2 ^ t := by
  unfold prepareIndexProb
  have hc : ‖((Real.sqrt (1 / 2) : ℂ) ^ t)‖ ^ 2 = ((1 : ℝ) / 2) ^ t := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), ← pow_mul,
      mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
  have hx : ∀ x : Fin (2 ^ g),
      ‖(((Real.sqrt (1 / 2) : ℂ) ^ t) • ∑ v, basisState (G v)) (prepareDataEquiv b g (j, x))‖ ^ 2 =
        ∑ v, if G v = prepareDataEquiv b g (j, x) then ((1 : ℝ) / 2) ^ t else 0 := by
    intro x
    rw [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    by_cases h : ∃ v, G v = prepareDataEquiv b g (j, x)
    · obtain ⟨v0, hv0⟩ := h
      rw [Finset.sum_eq_single v0, Finset.sum_eq_single v0]
      · rw [if_pos hv0, ← hv0]
        simp only [basisState, Pi.single_eq_same, mul_one]
        exact hc
      · intro v _ hv
        rw [if_neg]
        rw [← hv0]
        exact fun e ↦ hv (hG e)
      · intro h; exact absurd (Finset.mem_univ _) h
      · intro v _ hv
        have : prepareDataEquiv b g (j, x) ≠ G v := by
          rw [← hv0]; exact fun e ↦ hv (hG e.symm)
        simp [basisState, Pi.single_apply, this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · push_neg at h
      have h' : ∀ v, prepareDataEquiv b g (j, x) ≠ G v := fun v e ↦ h v e.symm
      simp [basisState, Pi.single_apply, h', h]
  rw [Finset.sum_congr rfl (fun x _ ↦ hx x), Finset.sum_comm]
  have hv : ∀ v, (∑ x : Fin (2 ^ g),
      if G v = prepareDataEquiv b g (j, x) then ((1 : ℝ) / 2) ^ t else 0) =
      if J v = j.val then ((1 : ℝ) / 2) ^ t else 0 := by
    intro v
    set p := (prepareDataEquiv b g).symm (G v) with hp
    have hGp : G v = prepareDataEquiv b g p := by rw [hp, Equiv.apply_symm_apply]
    have hJp : J v = p.1.val := by
      rw [← hJ v, hGp, prepareDataEquiv_val, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt p.1.isLt]
    by_cases hj : J v = j.val
    · rw [if_pos hj, Finset.sum_eq_single p.2]
      · rw [if_pos]
        rw [hGp]
        congr 1
        exact Prod.ext (Fin.ext (hJp.symm.trans hj)) rfl
      · intro x _ hx
        rw [if_neg]
        rw [hGp]
        intro e
        exact hx (congrArg Prod.snd ((prepareDataEquiv b g).injective e)).symm
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hj]
      refine Finset.sum_eq_zero fun x _ ↦ ?_
      rw [if_neg]
      rw [hGp]
      intro e
      have := congrArg Prod.fst ((prepareDataEquiv b g).injective e)
      exact hj (hJp.trans (congrArg Fin.val this))
  simp only [hv]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, one_div, inv_pow, div_eq_mul_inv]

/-! ### The prepared state -/

/-- The lookup table: alternate in the low `b` bits, keep value above. -/
def aliasF (b L μ : ℕ) (w : PrepareWeights L) (x : ℕ) : ℕ :=
  (AliasTable.aliasTable (2 ^ μ) (2 ^ b) (mass b L μ w) x).2 +
    2 ^ b * (AliasTable.aliasTable (2 ^ μ) (2 ^ b) (mass b L μ w) x).1

theorem gv_extZ_bits (D t : ℕ) (v : Fin (2 ^ t)) (k : ℕ) (hk : k < t) (hD : t ≤ D) :
    gv (extZ D t (basisBits t v)) k = ((v.val / 2 ^ k % 2 : ℕ) : ZMod 2) := by
  rw [gv, dif_pos (by omega)]
  simp only [extZ, dif_pos hk]
  exact basisBits_mk_apply v.val v.isLt ⟨k, hk⟩

theorem gv_extZ_high (D t : ℕ) (γ : Fin t → ZMod 2) (k : ℕ) (hk : t ≤ k) :
    gv (extZ D t γ) k = 0 := by
  unfold gv
  split_ifs with h
  · simp only [extZ, dif_neg (show ¬ k < t by omega)]
  · rfl

theorem rdv_extZ_lo (b μ D : ℕ) (hD : b + μ ≤ D) (v : Fin (2 ^ (b + μ))) :
    rdv (extZ D (b + μ) (basisBits (b + μ) v)) 0 b = v.val % 2 ^ b :=
  rdv_bits _ _ _ _ fun j hj ↦ by rw [zero_add, gv_extZ_bits D (b + μ) v j (by omega) hD]

theorem rdv_extZ_hi (b μ D : ℕ) (hD : b + μ ≤ D) (v : Fin (2 ^ (b + μ))) :
    rdv (extZ D (b + μ) (basisBits (b + μ) v)) b μ = v.val / 2 ^ b := by
  rw [rdv_bits _ _ _ (v.val / 2 ^ b) fun j hj ↦ by
    rw [gv_extZ_bits D (b + μ) v (b + j) (by omega) hD, Nat.div_div_eq_div_mul, ← pow_add]]
  apply Nat.mod_eq_of_lt
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, add_comm μ b]
  exact v.isLt

/-- The final index for the Hadamard outcome `v`: alias output of index `v mod 2^b` and uniform
sample `v / 2^b`. -/
theorem final_index (b L μ : ℕ) (w : PrepareWeights L) (hLb : L ≤ 2 ^ b) (hw : ∀ j, 0 ≤ w j)
    (hsum : 0 < prepareLambda w) (v : Fin (2 ^ (b + μ))) :
    rdv (Pbits b μ (aliasF b L μ w) (extZ (DD b μ) (b + μ) (basisBits (b + μ) v))) 0 b =
      AliasTable.aliasOut (2 ^ μ) (2 ^ b) (mass b L μ w) (v.val % 2 ^ b) (v.val / 2 ^ b) := by
  have hD : b + μ ≤ DD b μ := by unfold DD; omega
  have hx : v.val % 2 ^ b < 2 ^ b := Nat.mod_lt _ (by positivity)
  obtain ⟨hK, ha⟩ := AliasTable.aliasTable_lt (2 ^ μ) (2 ^ b) (mass b L μ w) (by positivity)
    (mass_sum w hLb hw hsum) (v.val % 2 ^ b) hx
  rw [rdv_Pbits b μ (aliasF b L μ w) _ (fun k hk ↦ gv_extZ_high _ _ _ k hk) _ _ ha hK
    (by rw [rdv_extZ_lo b μ _ hD]; rfl), rdv_extZ_lo b μ _ hD, rdv_extZ_hi b μ _ hD]
  rfl

/-- The number of Hadamard outcomes whose final index is `j` is `mass j`. -/
theorem final_card (b L μ : ℕ) (w : PrepareWeights L) (hLb : L ≤ 2 ^ b) (hw : ∀ j, 0 ≤ w j)
    (hsum : 0 < prepareLambda w) (j : ℕ) (hj : j < 2 ^ b) :
    (univ.filter (fun v : Fin (2 ^ (b + μ)) ↦
      AliasTable.aliasOut (2 ^ μ) (2 ^ b) (mass b L μ w) (v.val % 2 ^ b) (v.val / 2 ^ b) = j)).card
      = mass b L μ w j := by
  rw [← AliasTable.aliasOut_card (2 ^ μ) (2 ^ b) (mass b L μ w) (by positivity)
    (mass_sum w hLb hw hsum) j hj]
  have hP : 0 < 2 ^ b := by positivity
  refine Finset.card_bij' (fun v _ ↦ (v.val % 2 ^ b, v.val / 2 ^ b))
    (fun p hp ↦ ⟨p.1 + 2 ^ b * p.2, ?_⟩) (fun v hv ↦ ?_) (fun p hp ↦ ?_) (fun v _ ↦ ?_)
    (fun p hp ↦ ?_)
  · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    rw [pow_add]
    nlinarith [hp.1.1, hp.1.2]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨Nat.mod_lt _ hP, ?_⟩, hv⟩
    rw [Nat.div_lt_iff_lt_mul hP, ← pow_add, add_comm μ b]
    exact v.isLt
  · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp.1.1, Nat.add_mul_div_left _ _ hP,
      Nat.div_eq_of_lt hp.1.1, zero_add]
    exact hp.2
  · exact Fin.ext (Nat.mod_add_div _ _)
  · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp.1.1, Nat.add_mul_div_left _ _ hP,
      Nat.div_eq_of_lt hp.1.1, zero_add]

theorem basisBits_symm_mod (D b : ℕ) (hb : b ≤ D) (δ : BitAssignment D) :
    ((basisBits D).symm δ).val % 2 ^ b = rdv δ 0 b := by
  set u := (basisBits D).symm δ with hu
  have hδ : δ = basisBits D u := by rw [hu, Equiv.apply_symm_apply]
  symm
  refine rdv_bits _ _ _ _ fun j hj ↦ ?_
  rw [zero_add, hδ, gv, dif_pos (by omega)]
  exact basisBits_mk_apply u.val u.isLt ⟨j, by omega⟩

theorem alias_state (b L μ : ℕ) (w : PrepareWeights L) (hbμ : b + μ ≤ DD b μ) :
    (permutationUnitary (sigP b μ (aliasF b L μ w)) * (hAll (DD b μ) (b + μ) hbμ).eval).1 *ᵥ
        basisState 0 =
      ((Real.sqrt (1 / 2) : ℂ) ^ (b + μ)) • ∑ v : Fin (2 ^ (b + μ)),
        basisState ((basisBits (DD b μ)).symm
          (Pbits b μ (aliasF b L μ w) (extZ (DD b μ) (b + μ) (basisBits (b + μ) v)))) := by
  have h0 : (basisState (0 : Fin (2 ^ DD b μ)) : Fin (2 ^ DD b μ) → ℂ) =
      ket (0 : BitAssignment (DD b μ)) := by
    simp [ket, basisBits_symm_zero]
  rw [h0, mulVec_mul_unitary, hAll_ket, Matrix.mulVec_smul, Matrix.mulVec_sum]
  congr 1
  rw [← Equiv.sum_comp (basisBits (b + μ)) (fun γ ↦
    (permutationUnitary (sigP b μ (aliasF b L μ w))).1 *ᵥ ket (extZ (DD b μ) (b + μ) γ))]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  simp only [ket, basisState, permutationUnitary_mulVec_single]
  simp [sigP]

theorem alias_approx (b L μ : ℕ) (hLb : L ≤ 2 ^ b) (w : PrepareWeights L) (hw : ∀ j, 0 ≤ w j)
    (hsum : 0 < prepareLambda w) (hbμ : b + μ ≤ DD b μ) :
    PrepareApproximates b (b + 2 * μ + 1) L μ w
      ((permutationUnitary (sigP b μ (aliasF b L μ w)) * (hAll (DD b μ) (b + μ) hbμ).eval).1 *ᵥ
        basisState 0) := by
  have hbD : b ≤ DD b μ := by unfold DD; omega
  have hG : Function.Injective fun v : Fin (2 ^ (b + μ)) ↦ (basisBits (DD b μ)).symm
      (Pbits b μ (aliasF b L μ w) (extZ (DD b μ) (b + μ) (basisBits (b + μ) v))) := by
    intro v v' e
    have e1 := (Pbits b μ (aliasF b L μ w)).injective ((basisBits (DD b μ)).symm.injective e)
    apply (basisBits (b + μ)).injective
    funext i
    have := congrFun e1 ⟨i.val, by omega⟩
    simpa [extZ, i.isLt] using this
  have hprob : ∀ j : Fin (2 ^ b), prepareIndexProb b (b + 2 * μ + 1)
      ((permutationUnitary (sigP b μ (aliasF b L μ w)) * (hAll (DD b μ) (b + μ) hbμ).eval).1 *ᵥ
        basisState 0) j = (mass b L μ w j.val : ℝ) / 2 ^ (b + μ) := by
    intro j
    rw [alias_state, prob_inj b (b + 2 * μ + 1) (b + μ) _ hG
      (fun v ↦ AliasTable.aliasOut (2 ^ μ) (2 ^ b) (mass b L μ w) (v.val % 2 ^ b) (v.val / 2 ^ b))
      (fun v ↦ by
        show ((basisBits (DD b μ)).symm _).val % 2 ^ b = _
        rw [basisBits_symm_mod _ _ hbD, final_index b L μ w hLb hw hsum v]),
      final_card b L μ w hLb hw hsum j.val j.isLt]
  refine ⟨fun j hj ↦ ?_, fun j hj ↦ ?_⟩
  · rw [hprob, mass_zero w hsum _ hj]
    simp
  · rw [hprob]
    have hb := mass_bound (μ := μ) w hLb hw hsum j.val hj
    have hc : ((((mass b L μ w j.val : ℕ) : ℚ) / 2 ^ (b + μ) - w ⟨j.val, hj⟩ / prepareLambda w :
        ℚ) : ℝ) = (mass b L μ w j.val : ℝ) / 2 ^ (b + μ) -
          ((w ⟨j.val, hj⟩ / prepareLambda w : ℚ) : ℝ) := by
      push_cast; ring
    rw [← hc, ← Rat.cast_abs]
    have : (((1 : ℚ) / (2 ^ μ * L) : ℚ) : ℝ) = 1 / (2 ^ μ * L) := by push_cast; ring
    rw [← this]
    exact_mod_cast hb

/-! ### `T` count of the steps -/

theorem andCount_cswapSteps (c w_clean : Wire n) : ∀ (w : ℕ) (rA rB : QRegister w n),
    ((cswapSteps c w_clean w rA rB).map Step.andCount).sum = w := by
  intro w
  induction w with
  | zero => intro _ _; rfl
  | succ w ih =>
    intro rA rB
    rw [cswapSteps, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Step.andCount]
    omega

theorem andCount_aliasSteps (b μ : ℕ) {A : ℕ} (rData : QRegister (DD b μ) n)
    (rAnc : QRegister A n) (f : ℕ → ℕ) (hAb : b ≤ A) (hAμ : μ + 3 ≤ A)
    (hd : rData.DisjointWires rAnc) :
    ((aliasSteps b μ rData rAnc f hAb hAμ hd).map Step.andCount).sum ≤ 2 ^ b - 1 + 2 * μ + b := by
  have h1 := andCount_lookupSteps (b + μ) (rData.slice (b + μ) (b + μ) (by unfold DD; omega)) b
    none (rData.slice 0 b (by unfold DD; omega)) (rAnc.slice 0 b (by omega)) (tableBits (b + μ) f)
  rw [aliasSteps, stepsS1, stepsS2, stepsS3]
  simp only [List.map_append, List.sum_append, andCount_inv_rippleSteps, andCount_rippleSteps,
    andCount_cswapSteps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Step.andCount]
  omega

theorem count_alias {Var : Type} (v : Var) (b μ : ℕ) {A : ℕ} (rData : QRegister (DD b μ) n)
    (rAnc : QRegister A n) (f : ℕ → ℕ) (hAb : b ≤ A) (hAμ : μ + 3 ≤ A)
    (hd : rData.DisjointWires rAnc) (hbμ : b + μ ≤ DD b μ) :
    (DynamicCircuit.seq (.circuit ((hAll (DD b μ) (b + μ) hbμ).onRegister rData))
        (compileList v (aliasSteps b μ rData rAnc f hAb hAμ hd))).count PrimitiveGate.TOFF = 0 ∧
      (DynamicCircuit.seq (.circuit ((hAll (DD b μ) (b + μ) hbμ).onRegister rData))
        (compileList v (aliasSteps b μ rData rAnc f hAb hAμ hd))).count PrimitiveGate.T ≤
        4 * (2 ^ b - 1) + 8 * μ + 4 * b := by
  have hT := count_T_compileList v (aliasSteps b μ rData rAnc f hAb hAμ hd)
  have hA := andCount_aliasSteps b μ rData rAnc f hAb hAμ hd
  have h1 := count_hAll (DD b μ) (b + μ) hbμ PrimitiveGate.TOFF (by simp)
  have h2 := count_hAll (DD b μ) (b + μ) hbμ PrimitiveGate.T (by simp)
  simp only [DynamicCircuit.count, Circuit.count_onRegister, h1, h2, count_TOFF_compileList,
    zero_add]
  exact ⟨trivial, by omega⟩

end AliasPrepImpl

/-- Number of garbage qubits `prepareProgram` uses for `b` index qubits, `L` terms and precision
`μ`. Garbage starts in `|0⟩` and may end entangled with the index. It may not depend on the
weights. -/
def prepareGarbage (b L μ : ℕ) : ℕ := b + 2 * μ + 1

/-- Number of clean ancilla qubits `prepareProgram` uses for `b` index qubits, `L` terms and
precision `μ`. It may not depend on the weights. -/
def prepareAncillas (b L μ : ℕ) : ℕ := max b (μ + 3)

/-- Candidate `PREPARE` circuit for the weights `w` on `b + prepareGarbage b L μ` data wires
`rData` (`b` index wires, least significant first, followed by the garbage wires) and
`prepareAncillas b L μ` clean ancilla wires `rAnc`. -/
def prepareProgram {n : ℕ} (b L μ : ℕ) (w : PrepareWeights L)
    (rData : QRegister (b + prepareGarbage b L μ) n)
    (rAnc : QRegister (prepareAncillas b L μ) n) : DynamicCircuit Var n :=
  if hd : ∀ i j, rData i ≠ rAnc j then
    .seq (.circuit ((AliasPrepImpl.hAll (AliasPrepImpl.DD b μ) (b + μ)
        (by unfold AliasPrepImpl.DD; omega)).onRegister rData))
      (TableLookupSteps.compileList v (AliasPrepImpl.aliasSteps b μ rData rAnc
        (AliasPrepImpl.aliasF b L μ w) (le_max_left b (μ + 3)) (by unfold prepareAncillas; omega)
        (QRegister.disjoint_iff.mpr hd)))
  else .circuit .identity

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
  have hbμ : b + μ ≤ AliasPrepImpl.DD b μ := by unfold AliasPrepImpl.DD; omega
  refine ⟨permutationUnitary (AliasPrepImpl.sigP b μ (AliasPrepImpl.aliasF b L μ w)) *
      (AliasPrepImpl.hAll (AliasPrepImpl.DD b μ) (b + μ) hbμ).eval, ?_, ?_⟩
  · exact AliasPrepImpl.alias_approx b L μ hLb w hw hsum hbμ
  · intro n rData rAnc hdisj
    have hd' : ∀ i j, rData i ≠ rAnc j := QRegister.disjoint_iff.mp hdisj
    unfold prepareProgram
    rw [dif_pos hd']
    exact AliasPrepImpl.realizes_alias v b μ _ rData rAnc _ _ hdisj hbμ

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
def prepareTCost (b L μ : ℕ) : ℕ := 4 * (2 ^ b - 1) + 8 * μ + 4 * b

/-- For all `b`, `1 ≤ L ≤ 2^b`, `μ`, every weight table with `w_j ≥ 0` and `λ > 0`, and every
register placement, `prepareProgram` uses no `TOFF` gates and at most `prepareTCost b L μ` `T`
gates. -/
theorem prepare_t_cost (b L μ : ℕ) (hL : 1 ≤ L) (hLb : L ≤ 2 ^ b)
    (w : PrepareWeights L) (hw : ∀ j, 0 ≤ w j) (hsum : 0 < prepareLambda w) {n : ℕ}
    (rData : QRegister (b + prepareGarbage b L μ) n)
    (rAnc : QRegister (prepareAncillas b L μ) n) :
    (prepareProgram b L μ w rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      prepareTCount b L μ w rData rAnc ≤ prepareTCost b L μ := by
  have hbμ : b + μ ≤ AliasPrepImpl.DD b μ := by unfold AliasPrepImpl.DD; omega
  by_cases hd' : ∀ i j, rData i ≠ rAnc j
  · have hprog : prepareProgram b L μ w rData rAnc =
        .seq (.circuit ((AliasPrepImpl.hAll (AliasPrepImpl.DD b μ) (b + μ) hbμ).onRegister rData))
          (TableLookupSteps.compileList v (AliasPrepImpl.aliasSteps b μ rData rAnc
            (AliasPrepImpl.aliasF b L μ w) (le_max_left b (μ + 3))
            (by unfold prepareAncillas; omega) (QRegister.disjoint_iff.mpr hd'))) := by
      unfold prepareProgram
      rw [dif_pos hd']
    simp only [prepareTCount, hprog]
    exact AliasPrepImpl.count_alias v b μ rData rAnc _ _ _ _ hbμ
  · have hprog : prepareProgram b L μ w rData rAnc = .circuit .identity := by
      unfold prepareProgram
      rw [dif_neg hd']
    simp only [prepareTCount, hprog, DynamicCircuit.count]
    exact ⟨rfl, Nat.zero_le _⟩

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
def prepareB4Mu8SpacetimeCost : ℕ := 5040

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
  obtain ⟨h1, h2⟩ := prepare_t_cost PrepareSize.b4mu8.b PrepareSize.b4mu8.L PrepareSize.b4mu8.μ
    (by decide) (by decide) w hw hsum rData rAnc
  have hc : prepareTCost PrepareSize.b4mu8.b PrepareSize.b4mu8.L PrepareSize.b4mu8.μ = 140 := by
    decide
  have hq : prepareQubits PrepareSize.b4mu8.b PrepareSize.b4mu8.L PrepareSize.b4mu8.μ = 36 := by
    decide
  rw [hc] at h2
  rw [hq]
  refine ⟨h1, ?_⟩
  unfold prepareB4Mu8SpacetimeCost
  omega

end QuantumComputation.Specs
