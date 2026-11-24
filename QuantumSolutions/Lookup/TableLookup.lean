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
This file is a solution to the table-lookup specification `QuantumSpecs/Lookup/TableLookup.lean`: the spec
with its holes filled and its theorems proved, for unary-iteration lookup.

The sections between the markers `BEGIN GOOGLE-DERIVED` and `END GOOGLE-DERIVED` are copied
from google-deepmind/formal-quantum-computation, branch `discoveries` (commit a88de8f, 2026-11-17), files
`QuantumComputationDiscoveries/Primitives/Arcsin/Solution/{LowerKraus,StepSemantics,
EqualTableAdd}.lean`, Copyright 2026 Google LLC, licensed under the Apache License, Version 2.0.
Modification: the namespace `ArcsinImpl` is renamed to `TableLookupSteps`. Nothing else changed.
-/
module

public import QuantumComputation.Circuits.DynamicCircuit
public import QuantumComputation.Circuits.ResourceCounting
public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import QuantumComputation.Maths.Basis
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Table Lookup (`QROM`) and Measurement-Based Unlookup Specification

Parameterized specifications for loading classical data indexed by a quantum register: lookup
and unlookup, each also in a budgeted form whose clean-ancilla budget `a` is a size parameter
(the select-swap trade-off; see the section on budgets below).

**Lookup.** For a classical table `data : Fin L → Fin (2^w)` of `L ≤ 2^m` words of `w` bits,
realize `|x⟩|b⟩|0⟩^⊗a ↦ |x⟩|b ⊕ data(x)⟩|0⟩^⊗a` for every address `x < L` and every `w`-bit
target value `b`, where `⊕` is bitwise XOR. Addresses `x ≥ L` are unconstrained. The table is a
classical parameter of the program, so classical preprocessing of the table is free, as it is
for every quantum read-only memory construction in the literature.

**Unlookup.** For the same table, realize `|x⟩|data(x)⟩|0⟩^⊗a ↦ |x⟩|0⟩|0⟩^⊗a` for every address
`x < L`. Only inputs whose target already holds `data(x)` are constrained, so mid-circuit
measurement of the target followed by a classically controlled phase correction is allowed
(measurement-based uncomputation).

**Encoding.** The data register has `m + w` wires. Logical wire `0` is the least-significant bit
(library convention). Wires `0, ..., w - 1` hold the target `b` and wires `w, ..., w + m - 1`
hold the address `x`, matching `splitBasisEquiv m w` (index `b + 2^w * x`). Bit `i` of a word is
the radix-two digit `⌊b / 2^i⌋ mod 2` (`basisBits`).

**Resources.** Gates are Clifford + `T` with measurements and classical control. `TOFF` gates
are excluded, so each Toffoli is costed by its Clifford + `T` construction, such as `4` `T` gates
with an ancilla and a measurement (C. Jones, Phys. Rev. A 87, 022328 (2013)). Each spec has two
cost theorems, both for all sizes and all tables: a `T` count bound, and a spacetime bound
`T count * qubits` with `qubits = m + w + ancillas` (the data register plus the clean ancillas).
Each spec also has a pinned-size theorem at `LookupParams.l1024w32` (`L = 1024` entries of
`w = 32` bits, `m = 10`) that bounds `T count * qubits` by a closed constant, so a record at that
size is a single number.

**Reference baselines** (UNPROVED in Lean here; the record to beat):
* Lookup by unary iteration: `L - 1` Toffolis, so `4L - 4` `T` gates, with about `m` ancillas.
  R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, H. Neven,
  "Encoding electronic spectra in quantum circuits with linear T complexity",
  Phys. Rev. X 8, 041015 (2018), arXiv:1805.03662.
* Lookup by select-swap: fewer `T` gates at the cost of `λ w` extra qubits. G. H. Low,
  V. Kliuchnikov, L. Schaeffer, "Trading T-gates for dirty qubits in state preparation and
  unitary synthesis", arXiv:1812.00954.
* Unlookup by measurement-based uncomputation: about `L / k + k` Toffolis for a free choice of
  `k`. D. W. Berry, C. Gidney, M. Motta, J. R. McClean, R. Babbush, "Qubitization of arbitrary
  basis quantum chemistry leveraging sparsity and low rank factorization", Quantum 3, 208 (2019),
  arXiv:1902.02134, Appendix C; C. Gidney, "Windowed quantum arithmetic", arXiv:1905.07682.
-/

@[expose] public section

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

open Operator

/-- Sizes of a table lookup. -/
structure LookupParams where
  /-- Number of table entries `L`. -/
  L : ℕ
  /-- Address register width `m`. -/
  m : ℕ
  /-- Word width `w` of each entry. -/
  w : ℕ

/-- The sizes are meaningful: at least one entry, and every entry is addressable. -/
def LookupParams.Valid (p : LookupParams) : Prop :=
  0 < p.L ∧ p.L ≤ 2 ^ p.m

/-- A classical table of `p.L` words of `p.w` bits. -/
abbrev LookupTable (p : LookupParams) : Type := Fin p.L → Fin (2 ^ p.w)

/-- The table extended to all `2^m` addresses, with `0` at addresses `x ≥ L`. The value outside
the table never enters a constrained input of either spec. -/
def LookupTable.extend {p : LookupParams} (data : LookupTable p) :
    Fin (2 ^ p.m) → Fin (2 ^ p.w) :=
  fun x ↦ if h : x.val < p.L then data ⟨x.val, h⟩ else 0

/-!
## Bitwise XOR and the Ideal Basis Permutation
-/

/-- Bitwise XOR with the constant `c` on `w`-bit basis indices, through the little-endian bit
view `basisBits w` (addition in `Fin w → ZMod 2`). -/
def xorConstPerm {w : ℕ} (c : Fin (2 ^ w)) : Equiv.Perm (Fin (2 ^ w)) :=
  (basisBits w).trans ((Equiv.addRight (basisBits w c)).trans (basisBits w).symm)

/-- Basis permutation on `Fin (2 ^ (m + w))` for the table lookup
`|x⟩|b⟩ ↦ |x⟩|b ⊕ f(x)⟩` (address `x` on the high `m` wires, target `b` on the low `w` wires).
It is an involution. -/
def tableXorPerm {m w : ℕ} (f : Fin (2 ^ m) → Fin (2 ^ w)) :
    Equiv.Perm (Fin (2 ^ (m + w))) :=
  (splitBasisEquiv m w).trans
    ((Equiv.prodShear (Equiv.refl _) fun x ↦ xorConstPerm (f x)).trans
      (splitBasisEquiv m w).symm)

/-- Lookup inputs: any address `x < L` and any target value. -/
def lookupValidInputs (p : LookupParams) : Set (Fin (2 ^ (p.m + p.w))) :=
  {i | ((splitBasisEquiv p.m p.w) i).1.val < p.L}

/-- Unlookup inputs: any address `x < L` whose target holds exactly `data(x)`. -/
def unlookupValidInputs {p : LookupParams} (data : LookupTable p) :
    Set (Fin (2 ^ (p.m + p.w))) :=
  {i | ((splitBasisEquiv p.m p.w) i).1.val < p.L ∧
    ((splitBasisEquiv p.m p.w) i).2 = data.extend ((splitBasisEquiv p.m p.w) i).1}

/-!
## Classical Variables

Measurement outcomes may be stored in any number of variables `v i`. The store holds
measurement results only; it has no assignment and no loops.
-/

/-- Classical variables for measurement outcomes. -/
inductive TableLookup.Var where | v (i : ℕ) deriving DecidableEq, Inhabited

open TableLookup (Var)


/-!
## Implementation: unary-iteration lookup (Babbush et al. 2018)
-/

namespace TableLookupImpl

open Operator Matrix QProg Function TableLookupSteps HermitianMat
open scoped Matrix ComplexOrder MatrixOrder

theorem pow_le_pow_add (k m : ℕ) : 2 ^ k ≤ 2 ^ (k + m) :=
  Nat.pow_le_pow_right (by decide) (Nat.le_add_right k m)

theorem basisBits_castLE (k m : ℕ) (h : 2 ^ k ≤ 2 ^ (k + m)) (y : Fin (2 ^ k))
    (j : Fin (k + m)) :
    basisBits (k + m) (Fin.castLE h y) j =
      if hj : (j : ℕ) < k then basisBits k y ⟨j, hj⟩ else 0 := by
  rw [basisBits_eq_div_mod]
  split_ifs with hj
  · rw [basisBits_eq_div_mod]
    rfl
  · have h0 : y.val / 2 ^ j.val = 0 :=
      Nat.div_eq_of_lt (lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h0]

/-- The low `2^k` block of `Fin (2^(k+m))`. -/
def lowBlockEquiv (k m : ℕ) : Fin (2 ^ k) ≃ {i : Fin (2 ^ (k + m)) // i.val < 2 ^ k} where
  toFun y := ⟨Fin.castLE (pow_le_pow_add k m) y, y.isLt⟩
  invFun i := ⟨i.1.val, i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem basisOutcomesProjector_mulVec_ket {k n : ℕ} (r : QRegister k n)
    (S : Finset (Fin (2 ^ k))) (β : BitAssignment n) :
    (r.basisOutcomesProjector S).mulVec (ket β) = if localIdx r β ∈ S then ket β else 0 := by
  have hext : r.extractIndex ((basisBits n).symm β) = localIdx r β := by
    simp [QRegister.extractIndex]
  funext x
  rw [QRegister.basisOutcomesProjector, Matrix.mulVec_diagonal]
  by_cases hx : x = (basisBits n).symm β
  · subst hx
    rw [hext]
    split_ifs <;> simp
  · split_ifs <;> simp [ket, basisState, hx]

theorem bits_zero_of_localIdx_eq_zero {m n : ℕ} (r : QRegister m n) (β : BitAssignment n)
    (h : localIdx r β = 0) (i : Fin m) : β (r i) = 0 := by
  have h' : (fun i ↦ β (r i)) = basisBits m 0 := by
    rw [← h]
    simp [localIdx]
  have := congrFun h' i
  rw [this, basisBits_eq_div_mod]
  simp

theorem localIdx_concat_of_zero {k m n : ℕ} (rT : QRegister k n) (rA : QRegister m n)
    (hd : rT.DisjointWires rA) (β : BitAssignment n) (h0 : localIdx rA β = 0) :
    localIdx (rT.concat rA hd) β = Fin.castLE (pow_le_pow_add k m) (localIdx rT β) := by
  apply (basisBits (k + m)).injective
  funext j
  rw [basisBits_castLE]
  simp only [localIdx, Equiv.apply_symm_apply]
  induction j using Fin.addCases with
  | left i =>
    rw [QRegister.concat_apply_left, dif_pos (by simp)]
    rfl
  | right i =>
    rw [QRegister.concat_apply_right, dif_neg (by simp)]
    exact bits_zero_of_localIdx_eq_zero rA β h0 _

theorem writeReg_concat_castLE {k m n : ℕ} (rT : QRegister k n) (rA : QRegister m n)
    (hd : rT.DisjointWires rA) (β : BitAssignment n) (h0 : localIdx rA β = 0)
    (z : Fin (2 ^ k)) :
    writeReg β (rT.concat rA hd) (basisBits (k + m) (Fin.castLE (pow_le_pow_add k m) z)) =
      writeReg β rT (basisBits k z) := by
  funext w
  by_cases hT : w ∈ Set.range rT.wires
  · obtain ⟨i, rfl⟩ := hT
    have : rT i = rT.concat rA hd (Fin.castAdd m i) := (QRegister.concat_apply_left _ _ _ _).symm
    rw [writeReg_apply_reg]
    conv_lhs => rw [this]
    rw [writeReg_apply_reg, basisBits_castLE, dif_pos (by simp)]
    rfl
  · rw [writeReg_apply_of_not_mem _ _ _ _ hT]
    by_cases hA : w ∈ Set.range rA.wires
    · obtain ⟨i, rfl⟩ := hA
      have : rA i = rT.concat rA hd (Fin.natAdd k i) :=
        (QRegister.concat_apply_right _ _ _ _).symm
      conv_lhs => rw [this]
      rw [writeReg_apply_reg, basisBits_castLE, dif_neg (by simp),
        bits_zero_of_localIdx_eq_zero rA β h0 i]
    · rw [writeReg_apply_of_not_mem]
      rintro ⟨j, hj⟩
      refine Fin.addCases (motive := fun j ↦ (rT.concat rA hd) j = w → False)
        (fun i hi ↦ hT ⟨i, ?_⟩) (fun i hi ↦ hA ⟨i, ?_⟩) j hj
      · rw [← hi, QRegister.concat_apply_left]
      · rw [← hi, QRegister.concat_apply_right]

/-- Core inequality for a fixed outcome set `S ⊆ V`, given the classical action of `R` and of the
embedded extension `U` on clean, valid basis kets. -/
theorem fromBasisOutcomes_of_lowerKraus {Var : Type} [DecidableEq Var] {n k m : ℕ}
    [NeZero (2 ^ n)] (rT : QRegister k n) (rA : QRegister m n) (hd : rT.DisjointWires rA)
    (S : Finset (Fin (2 ^ k))) (U : Unitary (2 ^ (k + m))) {P : QProg Var (2 ^ n)}
    {R : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (hP : LowerKraus P R)
    (hkey : ∀ β, localIdx rA β = 0 → localIdx rT β ∈ S →
      R *ᵥ ket β = ((rT.concat rA hd).embedUnitary U).1 *ᵥ ket β) :
    RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rT S rA hd U P := by
  intro M s
  set Pv := rT.basisOutcomesProjector S with hPv
  set P0 := rA.basisOutcomeProjector 0 with hP0
  set E := (rT.concat rA hd).embedUnitary U with hE
  have hmat : R * (Pv * P0) = E.1 * (Pv * P0) := by
    apply matrix_ext_ket
    intro β
    simp only [← Matrix.mulVec_mulVec, hP0, basisOutcomeProjector_mulVec_ket, hPv]
    by_cases h0 : localIdx rA β = 0
    · by_cases hv : localIdx rT β ∈ S
      · rw [if_pos h0, basisOutcomesProjector_mulVec_ket, if_pos hv]
        exact hkey β h0 hv
      · rw [if_pos h0, basisOutcomesProjector_mulVec_ket, if_neg hv, Matrix.mulVec_zero,
          Matrix.mulVec_zero]
    · simp [h0]
  have hmat' : P0 * Pv * Rᴴ = P0 * Pv * E.1ᴴ := by
    have := congrArg conjTranspose hmat
    simpa [conjTranspose_mul, Matrix.mul_assoc, hPv, hP0] using this
  rw [← Subtype.coe_le_coe]
  change ((M.1.conj (star E).1).conj Pv).conj P0 ≤
    (((wp P (fun _ ↦ M) s).1).conj Pv).conj P0
  rw [conj_conj, conj_conj, Unitary.coe_star, Matrix.star_eq_conjTranspose,
    ← hmat', ← conj_conj, ← conj_conj]
  exact conj_mono (conj_mono (hP M s))

/-- Lift a `LowerKraus` bound whose matrix acts classically on valid, clean basis kets to
`RealizesCleanSubroutineOnEncoding`. -/
theorem realizesOnEncoding_of_lowerKraus {Var : Type} [DecidableEq Var] {n k m : ℕ}
    [NeZero (2 ^ n)] (rT : QRegister k n) (rA : QRegister m n) (hd : rT.DisjointWires rA)
    (V : Set (Fin (2 ^ k))) (σ : Equiv.Perm (Fin (2 ^ k))) {P : QProg Var (2 ^ n)}
    {R : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (hP : LowerKraus P R)
    (hR : ∀ β, localIdx rA β = 0 → localIdx rT β ∈ V →
      R *ᵥ ket β = ket (writeReg β rT (basisBits k (σ (localIdx rT β))))) :
    RealizesCleanSubroutineOnEncoding rT rA hd V σ P := by
  classical
  set τ : Equiv.Perm (Fin (2 ^ (k + m))) := σ.extendDomain (lowBlockEquiv k m) with hτ
  have hτapp : ∀ y, τ (Fin.castLE (pow_le_pow_add k m) y) =
      Fin.castLE (pow_le_pow_add k m) (σ y) := fun y ↦
    Equiv.Perm.extendDomain_apply_image σ (lowBlockEquiv k m) y
  refine ⟨permutationUnitary τ, ?_, ?_⟩
  · intro x _
    simp only [Function.Embedding.trans_apply, Function.Embedding.refl_apply,
      Fin.castLEEmb_apply, basisState]
    rw [permutationUnitary_mulVec_single, hτapp]
  · refine fromBasisOutcomes_of_lowerKraus rT rA hd _ _ hP fun β h0 hv ↦ ?_
    have hv' : localIdx rT β ∈ V :=
      ((@Finset.mem_filter _ V (fun o ↦ Classical.propDecidable (o ∈ V)) _ _).mp hv).2
    rw [hR β h0 hv', QRegister.embedUnitary_val]
    change _ = (rT.concat rA hd).embedMatrix ((τ⁻¹).permMatrix ℂ) *ᵥ ket β
    rw [embedMatrix_permMatrix_mulVec_ket, Equiv.Perm.inv_def, Equiv.symm_symm,
      localIdx_concat_of_zero rT rA hd β h0, hτapp,
      writeReg_concat_castLE rT rA hd β h0]

theorem splitBasisEquiv_fst_val (m w : ℕ) (i : Fin (2 ^ (m + w))) :
    ((splitBasisEquiv m w) i).1.val = i.val / 2 ^ w := by
  simp only [splitBasisEquiv, Equiv.trans_apply, finProdFinEquiv_symm_apply, Fin.divNat,
    finCongr_apply, Fin.val_cast]

theorem splitBasisEquiv_snd_val (m w : ℕ) (i : Fin (2 ^ (m + w))) :
    ((splitBasisEquiv m w) i).2.val = i.val % 2 ^ w := by
  simp only [splitBasisEquiv, Equiv.trans_apply, finProdFinEquiv_symm_apply, Fin.modNat,
    finCongr_apply, Fin.val_cast]

theorem splitBasisEquiv_symm_val (m w : ℕ) (x : Fin (2 ^ m)) (b : Fin (2 ^ w)) :
    ((splitBasisEquiv m w).symm (x, b)).val = b.val + 2 ^ w * x.val := by
  set i := (splitBasisEquiv m w).symm (x, b)
  have h := (splitBasisEquiv m w).apply_symm_apply (x, b)
  have h1 := splitBasisEquiv_fst_val m w i
  have h2 := splitBasisEquiv_snd_val m w i
  rw [h] at h1 h2
  simp only at h1 h2
  rw [h1, h2]
  exact (Nat.mod_add_div _ _).symm

theorem eq_writeReg_of_agree {k n : ℕ} (β γ : BitAssignment n) (r : QRegister k n)
    (hoff : ∀ w, w ∉ Set.range r.wires → γ w = β w) :
    γ = writeReg β r (basisBits k (localIdx r γ)) := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    rw [writeReg_apply_reg]
    simp [localIdx]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw, hoff w hw]

/-- Target wires (low `w` wires) of the data register. -/
abbrev targetReg {n : ℕ} (p : LookupParams) (rData : QRegister (p.m + p.w) n) :
    QRegister p.w n :=
  rData.slice 0 p.w (by omega)

/-- Address wires (high `m` wires) of the data register. -/
abbrev addrReg {n : ℕ} (p : LookupParams) (rData : QRegister (p.m + p.w) n) :
    QRegister p.m n :=
  rData.slice p.w p.m (by omega)

/-- The table as bit words indexed by natural-number addresses. -/
def lookupWords {p : LookupParams} (data : LookupTable p) : ℕ → BitAssignment p.w :=
  fun j ↦ if h : j < 2 ^ p.m then basisBits p.w (data.extend ⟨j, h⟩) else 0

/-- The unary-iteration lookup as a list of classical steps. -/
def lookupStepList {n : ℕ} (p : LookupParams) (data : LookupTable p)
    (rData : QRegister (p.m + p.w) n) (rAnc : QRegister p.m n) : List (Step n) :=
  lookupSteps p.w (targetReg p rData) p.m none (addrReg p rData) rAnc (lookupWords data)

theorem runList_lookupStepList {n : ℕ} (p : LookupParams) (data : LookupTable p)
    (rData : QRegister (p.m + p.w) n) (rAnc : QRegister p.m n) (hd : rData.DisjointWires rAnc)
    (β : BitAssignment n) (h0 : localIdx rAnc β = 0) :
    runList (lookupStepList p data rData rAnc) β =
      some (writeReg β rData
        (basisBits (p.m + p.w) (tableXorPerm data.extend (localIdx rData β)))) := by
  have hXW : (addrReg p rData).DisjointWires rAnc := hd.compose_left _
  have hYX : (targetReg p rData).DisjointWires (addrReg p rData) :=
    rData.slice_disjoint_of_le 0 p.w p.w p.m _ _ (by omega)
  have hXY : (addrReg p rData).DisjointWires (targetReg p rData) :=
    QRegister.disjoint_comm.mp hYX
  have hWY : rAnc.DisjointWires (targetReg p rData) :=
    QRegister.disjoint_comm.mp (hd.compose_left _)
  have hnone : ∀ (w : Wire n), CtrlNe none w := fun _ _ h ↦ by cases h
  rw [lookupStepList, runList_lookupSteps p.w _ p.m none _ rAnc _ hXW hXY hWY
    (fun _ ↦ hnone _) (fun _ ↦ hnone _) (fun _ ↦ hnone _) β
    (bits_zero_of_localIdx_eq_zero rAnc β h0)]
  congr 1
  set F : BitAssignment p.w := fun i ↦ β (targetReg p rData i) +
    ctrlVal none β * lookupWords data (localIdx (addrReg p rData) β) i with hF
  set γ := writeReg β (targetReg p rData) F with hγ
  have hoff : ∀ w, w ∉ Set.range rData.wires → γ w = β w := by
    intro w hw
    refine writeReg_apply_of_not_mem _ _ _ _ fun ⟨i, hi⟩ ↦ hw ⟨_, hi⟩
  refine (eq_writeReg_of_agree β γ rData hoff).trans ?_
  congr 2
  -- the index identity
  set X := localIdx (addrReg p rData) β with hX
  set Y := localIdx (targetReg p rData) β with hY
  have hv : (localIdx rData β).val = Y.val + 2 ^ p.w * X.val :=
    localIdx_val_split rData p.w p.m (by omega) β
  have hx' : (splitBasisEquiv p.m p.w (localIdx rData β)).1 = X := by
    apply Fin.ext
    rw [splitBasisEquiv_fst_val, hv, Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt Y.isLt, zero_add]
  have hb' : (splitBasisEquiv p.m p.w (localIdx rData β)).2 = Y := by
    apply Fin.ext
    rw [splitBasisEquiv_snd_val, hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt Y.isLt]
  have hγv : (localIdx rData γ).val = (localIdx (targetReg p rData) γ).val +
      2 ^ p.w * (localIdx (addrReg p rData) γ).val :=
    localIdx_val_split rData p.w p.m (by omega) γ
  have hγX : localIdx (addrReg p rData) γ = X :=
    localIdx_writeReg_of_disjoint _ _ _ hYX _
  have hγY : localIdx (targetReg p rData) γ = (basisBits p.w).symm F := localIdx_writeReg _ _ _
  have hFeq : (basisBits p.w).symm F = xorConstPerm (data.extend X) Y := by
    simp only [xorConstPerm, Equiv.trans_apply, Equiv.coe_addRight]
    congr 1
    funext i
    simp only [hF, ctrlVal, one_mul, lookupWords, dif_pos X.isLt, Fin.eta, Pi.add_apply, hY,
      localIdx, Equiv.apply_symm_apply]
  apply Fin.ext
  rw [hγv, hγX, hγY, hFeq, tableXorPerm, Equiv.trans_apply, Equiv.trans_apply,
    Equiv.prodShear_apply]
  simp only [Equiv.refl_apply]
  rw [hx', hb', splitBasisEquiv_symm_val]

variable {Var : Type} [DecidableEq Var]

theorem lookup_realizes {n : ℕ} (v : Var) (p : LookupParams) (data : LookupTable p)
    (rData : QRegister (p.m + p.w) n) (rAnc : QRegister p.m n) (hd : rData.DisjointWires rAnc)
    (V : Set (Fin (2 ^ (p.m + p.w)))) :
    RealizesCleanSubroutineOnEncoding rData rAnc hd V (tableXorPerm data.extend)
      (compileList v (lookupStepList p data rData rAnc)).compile := by
  haveI : NeZero (2 ^ n) := ⟨pow_ne_zero _ two_ne_zero⟩
  obtain ⟨R, hK, hR, -⟩ := exists_lowerKraus_compileList v (lookupStepList p data rData rAnc)
  exact realizesOnEncoding_of_lowerKraus rData rAnc hd V _ hK fun β h0 _ ↦
    hR _ _ (runList_lookupStepList p data rData rAnc hd β h0)

theorem lookup_count_TOFF {n : ℕ} (v : Var) (p : LookupParams) (data : LookupTable p)
    (rData : QRegister (p.m + p.w) n) (rAnc : QRegister p.m n) :
    (compileList v (lookupStepList p data rData rAnc)).count PrimitiveGate.TOFF = 0 :=
  count_TOFF_compileList v _

theorem lookup_count_T {n : ℕ} (v : Var) (p : LookupParams) (data : LookupTable p)
    (rData : QRegister (p.m + p.w) n) (rAnc : QRegister p.m n) :
    (compileList v (lookupStepList p data rData rAnc)).count PrimitiveGate.T ≤
      4 * (2 ^ p.m - 1) :=
  (count_T_compileList v _).trans
    (Nat.mul_le_mul_left 4 (andCount_lookupSteps _ _ _ _ _ _ _))

end TableLookupImpl

/-!
## Implementation: select-swap lookup (Low, Kliuchnikov, Schaeffer 2018)
-/

namespace SelectSwapImpl

open Operator Matrix QProg Function TableLookupSteps TableLookupImpl HermitianMat
open scoped Matrix ComplexOrder MatrixOrder

variable {n : ℕ}

/-- CNOT every wire of `rA` into the matching wire of `rY`. -/
def copySteps : (w : ℕ) → QRegister w n → QRegister w n → List (Step n)
  | 0, _, _ => []
  | w + 1, rA, rY => Step.cnot (rA 0) (rY 0) :: copySteps w (regTail rA) (regTail rY)

theorem runList_copySteps (w : ℕ) (rA rY : QRegister w n) (hd : rA.DisjointWires rY)
    (β : BitAssignment n) :
    runList (copySteps w rA rY) β = some (writeReg β rY (fun i ↦ β (rY i) + β (rA i))) := by
  induction w generalizing β with
  | zero =>
    rw [copySteps, runList_nil, show (fun i : Fin 0 ↦ β (rY i) + β (rA i)) =
      fun i ↦ β (rY i) from funext fun i ↦ i.elim0, writeReg_self]
  | succ w ih =>
    have hne : rA 0 ≠ rY 0 := hd.ne 0 0
    have hd' : (regTail rA).DisjointWires (regTail rY) := (hd.compose_left _).compose_right _
    rw [copySteps, runList_cons]
    simp only [Step.run, ne_eq, hne, not_false_eq_true, ↓reduceIte, Option.bind_some]
    rw [ih (regTail rA) (regTail rY) hd']
    congr 1
    rw [writeReg_succ β rY, writeReg_update_of_not_mem _ _ _ (zero_not_mem_regTail rY)]
    congr 2
    funext i
    rw [update_of_ne (regTail_ne_zero rY i), regTail_apply rA, update_of_ne (hd.ne i.succ 0),
      regTail_apply rY]

/-- Step-list `T`-count measure: the number of `and4t` steps. -/
def ac (L : List (Step n)) : ℕ := (L.map Step.andCount).sum

/-- Same for the inverted reversed list. -/
def aci (L : List (Step n)) : ℕ := ac (L.reverse.map Step.inv)

theorem ac_append (A B : List (Step n)) : ac (A ++ B) = ac A + ac B := by
  simp [ac]

theorem aci_append (A B : List (Step n)) : aci (A ++ B) = aci B + aci A := by
  simp [aci, ac, List.reverse_append, List.map_append, List.sum_append]

theorem ac_copySteps (w : ℕ) (rA rY : QRegister w n) : ac (copySteps w rA rY) = 0 := by
  induction w with
  | zero => rfl
  | succ w ih =>
    have := ih (regTail rA) (regTail rY)
    simp only [ac] at this ⊢
    rw [copySteps]
    simp [Step.andCount, this]

theorem ac_cswapSteps (c wc : Wire n) (w : ℕ) (rA rB : QRegister w n) :
    ac (cswapSteps c wc w rA rB) = w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    have := ih (regTail rA) (regTail rB)
    simp only [ac] at this ⊢
    rw [cswapSteps]
    simp [Step.andCount, this]
    omega

theorem aci_cswapSteps (c wc : Wire n) (w : ℕ) (rA rB : QRegister w n) :
    aci (cswapSteps c wc w rA rB) = w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    have := ih (regTail rA) (regTail rB)
    rw [cswapSteps, aci_append, this]
    simp [aci, ac, Step.inv, Step.andCount]

theorem ac_levelSwap (c wc : Wire n) (w : ℕ) (B : ℕ → QRegister w n) (off k : ℕ) :
    ac (levelSwap c wc w B off k) = k * w := by
  induction k with
  | zero => simp [levelSwap, ac]
  | succ k ih =>
    rw [levelSwap, ac_append, ih, ac_cswapSteps]
    ring

theorem aci_levelSwap (c wc : Wire n) (w : ℕ) (B : ℕ → QRegister w n) (off k : ℕ) :
    aci (levelSwap c wc w B off k) = k * w := by
  induction k with
  | zero => simp [levelSwap, aci, ac]
  | succ k ih =>
    rw [levelSwap, aci_append, ih, aci_cswapSteps]
    ring

theorem ac_swapTree (wc : Wire n) (w : ℕ) (B : ℕ → QRegister w n) (s : ℕ)
    (rc : QRegister s n) : ac (swapTree wc w B s rc) + w = 2 ^ s * w := by
  induction s with
  | zero => simp [swapTree, ac]
  | succ s ih =>
    have := ih (rc.slice 0 s (by omega))
    rw [swapTree, ac_append, ac_levelSwap, pow_succ]
    nlinarith

theorem aci_swapTree (wc : Wire n) (w : ℕ) (B : ℕ → QRegister w n) (s : ℕ)
    (rc : QRegister s n) : aci (swapTree wc w B s rc) + w = 2 ^ s * w := by
  induction s with
  | zero => simp [swapTree, aci, ac]
  | succ s ih =>
    have := ih (rc.slice 0 s (by omega))
    rw [swapTree, aci_append, aci_levelSwap, pow_succ]
    nlinarith

/-- The table entries as a function on natural-number addresses. -/
def fTab {p : LookupParams} (data : LookupTable p) : ℕ → ℕ :=
  fun x ↦ if h : x < 2 ^ p.m then (data.extend ⟨x, h⟩ : ℕ) else 0

/-- The entries `f (l + 2^s h)` for `l < 2^s`, `w` bits each, laid out side by side. -/
def wideTab (s w : ℕ) (f : ℕ → ℕ) (h : ℕ) : BitAssignment (2 ^ s * w) :=
  fun q ↦ tableBits w f ((q : ℕ) / w + 2 ^ s * h)
    ⟨(q : ℕ) % w, Nat.mod_lt _ (Nat.pos_of_ne_zero (by
      rintro rfl
      exact absurd q.isLt (by simp)))⟩

theorem writeReg_wideTab_dataBlock (β : BitAssignment n) (s w : ℕ) (f : ℕ → ℕ)
    (rD : QRegister (2 ^ s * w) n) (h l : ℕ) (hl : l < 2 ^ s) (i : Fin w) :
    writeReg β rD (wideTab s w f h) (dataBlock s w rD l i) =
      tableBits w f (l + 2 ^ s * h) i := by
  have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; exact i.elim0)
  have hd : (l * w + i) / w = l := by
    rw [add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt i.isLt, zero_add]
  have hm : (l * w + i) % w = i := by
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
  rw [dataBlock, QRegister.slice_apply, writeReg_apply_reg, wideTab]
  simp only [Nat.mod_eq_of_lt hl, hd, hm]

/-- Select-swap lookup steps. -/
def ssSteps (p : LookupParams) (s : ℕ) (hs : s ≤ p.m) (f : ℕ → ℕ)
    (rData : QRegister (p.m + p.w) n) (rD : QRegister (2 ^ s * p.w) n)
    (rW : QRegister (p.m - s) n) (ci : Wire n) : List (Step n) :=
  lookupSteps (2 ^ s * p.w) rD (p.m - s) none (rData.slice (p.w + s) (p.m - s) (by omega)) rW
      (wideTab s p.w f) ++
    swapTree ci p.w (dataBlock s p.w rD) s (rData.slice p.w s (by omega)) ++
    copySteps p.w (dataBlock s p.w rD 0) (rData.slice 0 p.w (by omega)) ++
    (swapTree ci p.w (dataBlock s p.w rD) s (rData.slice p.w s (by omega))).reverse.map
      Step.inv ++
    lookupSteps (2 ^ s * p.w) rD (p.m - s) none (rData.slice (p.w + s) (p.m - s) (by omega)) rW
      (wideTab s p.w f)

theorem runList_ssSteps (p : LookupParams) (s : ℕ) (hs : s ≤ p.m) (f : ℕ → ℕ)
    (rData : QRegister (p.m + p.w) n) (rD : QRegister (2 ^ s * p.w) n)
    (rW : QRegister (p.m - s) n) (ci : Wire n)
    (hDl : rD.DisjointWires (rData.slice p.w s (by omega)))
    (hDh : rD.DisjointWires (rData.slice (p.w + s) (p.m - s) (by omega)))
    (hDW : rD.DisjointWires rW)
    (hDY : rD.DisjointWires (rData.slice 0 p.w (by omega)))
    (hlY : (rData.slice p.w s (by omega)).DisjointWires (rData.slice 0 p.w (by omega)))
    (hhW : (rData.slice (p.w + s) (p.m - s) (by omega)).DisjointWires rW)
    (hhY : (rData.slice (p.w + s) (p.m - s) (by omega)).DisjointWires
      (rData.slice 0 p.w (by omega)))
    (hWY : rW.DisjointWires (rData.slice 0 p.w (by omega)))
    (hiD : ci ∉ Set.range rD.wires) (hiXl : ci ∉ Set.range (rData.slice p.w s (by omega)).wires)
    (hiY : ci ∉ Set.range (rData.slice 0 p.w (by omega)).wires) (β : BitAssignment n)
    (hD : ∀ i, β (rD i) = 0) (hW : ∀ i, β (rW i) = 0) (hci : β ci = 0) :
    runList (ssSteps p s hs f rData rD rW ci) β =
      some (writeReg β (rData.slice 0 p.w (by omega)) (fun i ↦
        β (rData.slice 0 p.w (by omega) i) +
          tableBits p.w f ((localIdx (rData.slice p.w s (by omega)) β : ℕ) +
            2 ^ s * (localIdx (rData.slice (p.w + s) (p.m - s) (by omega)) β : ℕ)) i)) := by
  set rXl := rData.slice p.w s (by omega) with hrXl
  set rXh := rData.slice (p.w + s) (p.m - s) (by omega) with hrXh
  set rY := rData.slice 0 p.w (by omega) with hrY
  set B := dataBlock s p.w rD with hBdef
  set S := swapTree ci p.w B s rXl with hS
  have hnB : ∀ {v}, v ∉ Set.range rD.wires → ∀ l, v ∉ Set.range (B l).wires :=
    fun hv _ ↦ not_mem_slice hv _ _ _
  have hlook := fun β' ↦ runList_lookupSteps (2 ^ s * p.w) rD (p.m - s) none rXh rW
    (wideTab s p.w f) hhW
    (QRegister.disjoint_comm.mp hDh) (QRegister.disjoint_comm.mp hDW)
    (fun _ ↦ ctrlNe_none _) (fun _ ↦ ctrlNe_none _) (fun _ ↦ ctrlNe_none _) β'
  set x := (localIdx rXl β : ℕ) + 2 ^ s * (localIdx rXh β : ℕ) with hx
  set β1 := writeReg β rD (wideTab s p.w f (localIdx rXh β)) with hβ1
  have h1 : runList (lookupSteps (2 ^ s * p.w) rD (p.m - s) none rXh rW (wideTab s p.w f)) β =
      some β1 := by
    rw [hlook β hW]
    simp only [hD, ctrlVal, zero_add, one_mul]
    rfl
  have hb1 : ∀ v, v ∉ Set.range rD.wires → β1 v = β v := fun v hv ↦
    writeReg_apply_of_not_mem _ _ _ _ hv
  obtain ⟨β2, h2, hfr2_B, h2B⟩ := runList_swapTree ci p.w B s rXl
    (fun l l' hl hl' h ↦ dataBlock_disjoint s p.w rD hl hl' h)
    (fun j ↦ hnB (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDl) j))
    hiXl (hnB hiD) β1 (by rw [hb1 _ hiD, hci])
  have hfr2 : ∀ v, v ∉ Set.range rD.wires → β2 v = β1 v := fun v hv ↦ hfr2_B v (hnB hv)
  have hB0 : ∀ i, β2 (B 0 i) = tableBits p.w f x i := fun i ↦ by
    have hl := (localIdx rXl β).isLt
    rw [h2B, localIdx_writeReg_of_disjoint _ _ _ hDl, hβ1,
      writeReg_wideTab_dataBlock _ _ _ _ _ _ _ hl]
  have hrY2 : ∀ i, β2 (rY i) = β (rY i) := fun i ↦ by
    rw [hfr2 _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDY) i),
      hb1 _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDY) i)]
  set γ : BitAssignment p.w := fun i ↦ β (rY i) + tableBits p.w f x i with hγ
  have h3 : runList (copySteps p.w (B 0) rY) β2 = some (writeReg β2 rY γ) := by
    rw [runList_copySteps p.w (B 0) rY (hDY.compose_left _)]
    congr 2
    funext i
    rw [hB0, hrY2]
  have h4 : runList (S.reverse.map Step.inv) (writeReg β2 rY γ) = some (writeReg β1 rY γ) := by
    rw [runList_writeReg_of_avoids _ rY (fun st hst i ↦ by
        obtain ⟨st', hst', rfl⟩ := List.mem_map.mp hst
        exact Step.avoids_inv (swapTree_avoids ci p.w B s rXl _
          (fun h ↦ hiY ⟨i, h.symm⟩)
          (not_mem_of_disjoint (QRegister.disjoint_comm.mp hlY) i)
          (hnB (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDY) i))
          st' (List.mem_reverse.mp hst'))),
      runList_inv (swapTree_noUnxor ci p.w B s rXl) h2, Option.map_some]
  have hγ' : writeReg β1 rY γ = writeReg β1 rY γ := rfl
  rw [ssSteps, runList_append, runList_append, runList_append, runList_append, h1,
    Option.bind_some, ← hS, h2, Option.bind_some, h3, Option.bind_some, h4, Option.bind_some,
    hlook _ (fun i ↦ by
      rw [writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hWY i),
        hb1 _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDW) i), hW])]
  simp only [localIdx_writeReg_of_disjoint _ _ _ (QRegister.disjoint_comm.mp hhY),
    hβ1, localIdx_writeReg_of_disjoint _ _ _ hDh,
    writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hDY _), writeReg_apply_reg, ctrlVal,
    one_mul, CharTwo.add_self_eq_zero]
  rw [writeReg_comm _ rY rD (QRegister.disjoint_comm.mp hDY), writeReg_writeReg,
    show (fun _ : Fin (2 ^ s * p.w) ↦ (0 : ZMod 2)) = fun i ↦ β (rD i) from
      funext fun i ↦ (hD i).symm, writeReg_self]

end SelectSwapImpl

namespace SelectSwapImpl

open Operator Matrix QProg Function TableLookupSteps TableLookupImpl HermitianMat
open scoped Matrix ComplexOrder MatrixOrder

variable {n : ℕ}

/-- `T` count of select-swap with swap depth `s`. -/
def ssT (m w s : ℕ) : ℕ := 8 * (2 ^ (m - s) - 1) + 8 * (2 ^ s - 1) * w

/-- Clean ancillas of select-swap with swap depth `s`. -/
def ssA (m w s : ℕ) : ℕ := 2 ^ s * w + (m - s) + 1

/-- Swap depth in `0..m` minimizing `ssT` among those with `ssA ≤ a` (ties to the smaller `s`). -/
def ssBest (m w a : ℕ) : ℕ :=
  (List.range (m + 1)).foldl
    (fun b s ↦ if ssA m w s ≤ a ∧ (a < ssA m w b ∨ ssT m w s < ssT m w b) then s else b) 0

/-- Select-swap at the chosen depth pays off and fits the budget. -/
abbrev ssCond (m w a : ℕ) : Prop :=
  ssBest m w a ≤ m ∧ ssA m w (ssBest m w a) ≤ a ∧ ssT m w (ssBest m w a) < 4 * (2 ^ m - 1)

/-- Number of clean ancillas. -/
def ssAnc (m w a : ℕ) : ℕ := if ssCond m w a then ssA m w (ssBest m w a) else m

theorem ssAnc_pos {m w a : ℕ} (h : ssCond m w a) : ssAnc m w a = ssA m w (ssBest m w a) := if_pos h

theorem ssAnc_neg {m w a : ℕ} (h : ¬ ssCond m w a) : ssAnc m w a = m := if_neg h

/-- Cast a register along an equality of sizes. -/
def castReg {N M : ℕ} (h : N = M) (r : QRegister N n) : QRegister M n := h ▸ r

/-- The select-swap lookup with swap depth `s` on data wires `rData` and ancillas `rAnc`. -/
def ssProgSteps (p : LookupParams) (s : ℕ) (data : LookupTable p)
    (rData : QRegister (p.m + p.w) n)
    {N : ℕ} (rAnc : QRegister N n) (hN : 2 ^ s * p.w + (p.m - s) + 1 ≤ N) (hm : s ≤ p.m) :
    List (Step n) :=
  ssSteps p s hm (fTab data) rData (rAnc.slice 0 (2 ^ s * p.w) (by omega))
    (rAnc.slice (2 ^ s * p.w) (p.m - s) (by omega))
    (rAnc ⟨2 ^ s * p.w + (p.m - s), by omega⟩)

theorem hbits {p : LookupParams} (data : LookupTable p) (x : ℕ) (hx : x < 2 ^ p.m) :
    tableBits p.w (fTab data) x = lookupWords data x := by
  rw [tableBits_eq, lookupWords, dif_pos hx]
  congr 1
  apply Fin.ext
  simp only [fTab, dif_pos hx]
  exact Nat.mod_eq_of_lt (data.extend ⟨x, hx⟩).isLt

theorem target_xor_eq {p : LookupParams} (data : LookupTable p) (rData : QRegister (p.m + p.w) n)
    (β : BitAssignment n) :
    writeReg β (targetReg p rData) (fun i ↦ β (targetReg p rData i) +
        lookupWords data (localIdx (addrReg p rData) β) i) =
      writeReg β rData (basisBits (p.m + p.w) (tableXorPerm data.extend (localIdx rData β))) := by
  have hYX : (targetReg p rData).DisjointWires (addrReg p rData) :=
    rData.slice_disjoint_of_le 0 p.w p.w p.m _ _ (by omega)
  set F : BitAssignment p.w := fun i ↦ β (targetReg p rData i) +
    lookupWords data (localIdx (addrReg p rData) β) i with hF
  set γ := writeReg β (targetReg p rData) F with hγ
  have hoff : ∀ w, w ∉ Set.range rData.wires → γ w = β w := by
    intro w hw
    refine writeReg_apply_of_not_mem _ _ _ _ fun ⟨i, hi⟩ ↦ hw ⟨_, hi⟩
  refine (eq_writeReg_of_agree β γ rData hoff).trans ?_
  congr 2
  set X := localIdx (addrReg p rData) β with hX
  set Y := localIdx (targetReg p rData) β with hY
  have hv : (localIdx rData β).val = Y.val + 2 ^ p.w * X.val :=
    localIdx_val_split rData p.w p.m (by omega) β
  have hx' : (splitBasisEquiv p.m p.w (localIdx rData β)).1 = X := by
    apply Fin.ext
    rw [splitBasisEquiv_fst_val, hv, Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt Y.isLt, zero_add]
  have hb' : (splitBasisEquiv p.m p.w (localIdx rData β)).2 = Y := by
    apply Fin.ext
    rw [splitBasisEquiv_snd_val, hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt Y.isLt]
  have hγv : (localIdx rData γ).val = (localIdx (targetReg p rData) γ).val +
      2 ^ p.w * (localIdx (addrReg p rData) γ).val :=
    localIdx_val_split rData p.w p.m (by omega) γ
  have hγX : localIdx (addrReg p rData) γ = X :=
    localIdx_writeReg_of_disjoint _ _ _ hYX _
  have hγY : localIdx (targetReg p rData) γ = (basisBits p.w).symm F := localIdx_writeReg _ _ _
  have hFeq : (basisBits p.w).symm F = xorConstPerm (data.extend X) Y := by
    simp only [xorConstPerm, Equiv.trans_apply, Equiv.coe_addRight]
    congr 1
    funext i
    simp only [hF, lookupWords, dif_pos X.isLt, Fin.eta, Pi.add_apply, hY,
      localIdx, Equiv.apply_symm_apply]
  apply Fin.ext
  rw [hγv, hγX, hγY, hFeq, tableXorPerm, Equiv.trans_apply, Equiv.trans_apply,
    Equiv.prodShear_apply]
  simp only [Equiv.refl_apply]
  rw [hx', hb', splitBasisEquiv_symm_val]

theorem runList_ssProgSteps (p : LookupParams) (s : ℕ) (data : LookupTable p)
    (rData : QRegister (p.m + p.w) n) {N : ℕ} (rAnc : QRegister N n)
    (hN : 2 ^ s * p.w + (p.m - s) + 1 ≤ N) (hm : s ≤ p.m) (hd : rData.DisjointWires rAnc)
    (β : BitAssignment n) (h0 : localIdx rAnc β = 0) :
    runList (ssProgSteps p s data rData rAnc hN hm) β =
      some (writeReg β rData
        (basisBits (p.m + p.w) (tableXorPerm data.extend (localIdx rData β)))) := by
  have hclean := eq_zero_of_localIdx_eq_zero rAnc β h0
  have hDA : ∀ {a b : ℕ} (r : QRegister a (p.m + p.w)) (r' : QRegister b N),
      (rAnc.compose r').DisjointWires (rData.compose r) := fun _ _ ↦
    QRegister.disjoint_comm.mp ((hd.compose_left _).compose_right _)
  have hx : (localIdx (addrReg p rData) β : ℕ) =
      (localIdx (rData.slice p.w s (by omega)) β : ℕ) +
        2 ^ s * (localIdx (rData.slice (p.w + s) (p.m - s) (by omega)) β : ℕ) := by
    rw [localIdx_val_split (addrReg p rData) s (p.m - s) (by omega)]
    simp only [localIdx_slice_slice, add_zero]
  have hD0 : ∀ i, β (rAnc.slice 0 (2 ^ s * p.w) (by omega) i) = 0 := fun _ ↦ hclean _
  have hW0 : ∀ i, β (rAnc.slice (2 ^ s * p.w) (p.m - s) (by omega) i) = 0 := fun _ ↦ hclean _
  rw [ssProgSteps, runList_ssSteps p s hm (fTab data) rData _ _ _ (hDA _ _) (hDA _ _)
    (QRegister.slice_disjoint_of_le rAnc _ _ _ _ (by omega) (by omega) (by omega)) (hDA _ _)
    (QRegister.disjoint_comm.mp
      (QRegister.slice_disjoint_of_le rData _ _ _ _ (by omega) (by omega) (by omega)))
    (QRegister.disjoint_comm.mp (hDA _ _))
    (QRegister.disjoint_comm.mp
      (QRegister.slice_disjoint_of_le rData _ _ _ _ (by omega) (by omega) (by omega)))
    (hDA _ _)
    (apply_not_mem_slice rAnc _ 0 _ (by omega) (Or.inr (by simp)))
    (fun ⟨_, h⟩ ↦ hd.ne _ _ h)
    (fun ⟨_, h⟩ ↦ hd.ne _ _ h)
    β hD0 hW0 (hclean _)]
  congr 1
  rw [← target_xor_eq data rData β]
  congr 1
  funext i
  have this' := congrFun (hbits data _ (localIdx (addrReg p rData) β).isLt) i
  rw [← hx, this']

end SelectSwapImpl

namespace SelectSwapImpl

open Operator Matrix QProg Function TableLookupSteps TableLookupImpl HermitianMat
open scoped Matrix ComplexOrder MatrixOrder

variable {n : ℕ}

theorem ssProg_realizes (p : LookupParams) (s : ℕ) (data : LookupTable p)
    (rData : QRegister (p.m + p.w) n) {N : ℕ} (rAnc : QRegister N n)
    (hN : 2 ^ s * p.w + (p.m - s) + 1 ≤ N) (hm : s ≤ p.m) (hd : rData.DisjointWires rAnc)
    (V : Set (Fin (2 ^ (p.m + p.w)))) :
    RealizesCleanSubroutineOnEncoding rData rAnc hd V (tableXorPerm data.extend)
      (compileList (Var.v 0) (ssProgSteps p s data rData rAnc hN hm)).compile := by
  haveI : NeZero (2 ^ n) := ⟨pow_ne_zero _ two_ne_zero⟩
  obtain ⟨R, hK, hR, -⟩ :=
    exists_lowerKraus_compileList (Var.v 0) (ssProgSteps p s data rData rAnc hN hm)
  exact realizesOnEncoding_of_lowerKraus rData rAnc hd V _ hK fun β h0 _ ↦
    hR _ _ (runList_ssProgSteps p s data rData rAnc hN hm hd β h0)

theorem castReg_realizes (p : LookupParams) (data : LookupTable p)
    (rData : QRegister (p.m + p.w) n) {N : ℕ} (hN : N = p.m) (rAnc : QRegister N n)
    (hd : rData.DisjointWires rAnc) (V : Set (Fin (2 ^ (p.m + p.w)))) :
    RealizesCleanSubroutineOnEncoding rData rAnc hd V (tableXorPerm data.extend)
      (compileList (Var.v 0) (lookupStepList p data rData (castReg hN rAnc))).compile := by
  subst hN
  exact lookup_realizes (Var.v 0) p data rData rAnc hd V

theorem ac_ssSteps (p : LookupParams) (s : ℕ) (hs : s ≤ p.m) (f : ℕ → ℕ)
    (rData : QRegister (p.m + p.w) n) (rD : QRegister (2 ^ s * p.w) n)
    (rW : QRegister (p.m - s) n) (ci : Wire n) :
    ac (ssSteps p s hs f rData rD rW ci) + 2 * p.w ≤ 2 * (2 ^ (p.m - s) - 1) + 2 * (2 ^ s * p.w) := by
  have h1 : ac (lookupSteps (2 ^ s * p.w) rD (p.m - s) none
      (rData.slice (p.w + s) (p.m - s) (by omega)) rW (wideTab s p.w f)) ≤ 2 ^ (p.m - s) - 1 :=
    andCount_lookupSteps _ _ _ _ _ _ _
  have h2 := ac_swapTree ci p.w (dataBlock s p.w rD) s (rData.slice p.w s (by omega))
  have h3 := aci_swapTree ci p.w (dataBlock s p.w rD) s (rData.slice p.w s (by omega))
  have h4 := ac_copySteps p.w (dataBlock s p.w rD 0) (rData.slice 0 p.w (by omega))
  have h3' : ac ((swapTree ci p.w (dataBlock s p.w rD) s
      (rData.slice p.w s (by omega))).reverse.map Step.inv) + p.w = 2 ^ s * p.w := h3
  simp only [ssSteps, ac_append]
  omega

theorem ssProg_count_T (p : LookupParams) (s : ℕ) (data : LookupTable p)
    (rData : QRegister (p.m + p.w) n) {N : ℕ} (rAnc : QRegister N n)
    (hN : 2 ^ s * p.w + (p.m - s) + 1 ≤ N) (hm : s ≤ p.m) :
    (compileList (Var.v 0) (ssProgSteps p s data rData rAnc hN hm)).count PrimitiveGate.T ≤
      ssT p.m p.w s := by
  refine (count_T_compileList _ _).trans ?_
  have h : ac (ssProgSteps p s data rData rAnc hN hm) + 2 * p.w ≤
      2 * (2 ^ (p.m - s) - 1) + 2 * (2 ^ s * p.w) := ac_ssSteps p s hm _ _ _ _ _
  have e : ((ssProgSteps p s data rData rAnc hN hm).map Step.andCount).sum =
    ac (ssProgSteps p s data rData rAnc hN hm) := rfl
  rw [e]
  have h2 : 8 * (2 ^ s - 1) * p.w + 8 * p.w = 8 * (2 ^ s * p.w) := by
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ s = k + 1 := ⟨2 ^ s - 1, by have := @Nat.one_le_two_pow s; omega⟩
    rw [hk, Nat.add_sub_cancel]
    ring
  unfold ssT
  omega

end SelectSwapImpl


/-!
## Lookup: Holes Filled and Theorems Proved
-/

open TableLookupSteps TableLookupImpl

/-- Number of clean ancilla qubits `qromLookupProgram` uses for sizes `p`. -/
def qromLookupAncillas (p : LookupParams) : ℕ := p.m

/-- Lookup circuit for table `data` on the `p.m + p.w` data wires `rData` (`p.w` target wires
followed by `p.m` address wires) and `qromLookupAncillas p` clean ancilla wires `rAnc`. -/
def qromLookupProgram {n : ℕ} (p : LookupParams) (data : LookupTable p)
    (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromLookupAncillas p) n) : DynamicCircuit Var n :=
  compileList (Var.v 0) (lookupStepList p data rData rAnc)

/-- For valid sizes and every table, `qromLookupProgram` realizes `|x⟩|b⟩ ↦ |x⟩|b ⊕ data(x)⟩`
on every address `x < L` and every target `b`, as an exact clean subroutine across all disjoint
register placements. -/
theorem qromLookup_correctness (p : LookupParams) (hp : p.Valid) (data : LookupTable p)
    {n : ℕ} (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromLookupAncillas p) n) (hdisj : rData.DisjointWires rAnc) :
    RealizesCleanSubroutineOnEncoding rData rAnc hdisj (lookupValidInputs p)
      (tableXorPerm data.extend) (qromLookupProgram p data rData rAnc).compile := by
  exact lookup_realizes (Var.v 0) p data rData rAnc hdisj _

/-- Claimed `T` count of the lookup, as a function of the sizes. -/
def qromLookupTCost (p : LookupParams) : ℕ := 4 * (2 ^ p.m - 1)

/-- For valid sizes, every table and every placement, the lookup uses no `TOFF` gates and at
most `qromLookupTCost p` `T` gates. -/
theorem qromLookup_t_cost (p : LookupParams) (hp : p.Valid) (data : LookupTable p)
    {n : ℕ} (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromLookupAncillas p) n) :
    (qromLookupProgram p data rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (qromLookupProgram p data rData rAnc).count PrimitiveGate.T ≤ qromLookupTCost p := by
  exact ⟨lookup_count_TOFF (Var.v 0) p data rData rAnc,
    lookup_count_T (Var.v 0) p data rData rAnc⟩

/-- Claimed spacetime cost `T count * (m + w + ancillas)` of the lookup, as a function of the
sizes. -/
def qromLookupSpacetimeCost (p : LookupParams) : ℕ := 4 * (2 ^ p.m - 1) * (p.m + p.w + p.m)

/-- For valid sizes, every table and every placement, the lookup uses no `TOFF` gates and has
`T count * (p.m + p.w + qromLookupAncillas p) ≤ qromLookupSpacetimeCost p`. -/
theorem qromLookup_spacetime_cost (p : LookupParams) (hp : p.Valid) (data : LookupTable p)
    {n : ℕ} (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromLookupAncillas p) n) :
    (qromLookupProgram p data rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (qromLookupProgram p data rData rAnc).count PrimitiveGate.T *
          (p.m + p.w + qromLookupAncillas p) ≤ qromLookupSpacetimeCost p := by
  exact ⟨lookup_count_TOFF (Var.v 0) p data rData rAnc,
    Nat.mul_le_mul_right _ (lookup_count_T (Var.v 0) p data rData rAnc)⟩

/-- Pinned size for single-number records: `L = 1024` entries of `w = 32` bits, `m = 10`. -/
abbrev LookupParams.l1024w32 : LookupParams where
  L := 1024
  m := 10
  w := 32

/-- Claimed spacetime cost bound for the lookup at `LookupParams.l1024w32`:
`4 * (2^10 - 1) * (10 + 32 + 10) = 212784`. -/
def qromLookupL1024W32ConstCost : ℕ := 212784

/-- At `LookupParams.l1024w32`, for every table and every placement, the lookup uses no `TOFF`
gates and has `T count * (m + w + qromLookupAncillas) ≤ qromLookupL1024W32ConstCost`. -/
theorem qromLookup_l1024w32_const_cost (data : LookupTable .l1024w32) {n : ℕ}
    (rData : QRegister (LookupParams.l1024w32.m + LookupParams.l1024w32.w) n)
    (rAnc : QRegister (qromLookupAncillas .l1024w32) n) :
    (qromLookupProgram .l1024w32 data rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (qromLookupProgram .l1024w32 data rData rAnc).count PrimitiveGate.T *
          (LookupParams.l1024w32.m + LookupParams.l1024w32.w + qromLookupAncillas .l1024w32) ≤
        qromLookupL1024W32ConstCost := by
  exact ⟨lookup_count_TOFF (Var.v 0) _ data rData rAnc,
    (Nat.mul_le_mul_right _ (lookup_count_T (Var.v 0) _ data rData rAnc)).trans (by decide)⟩

/-!
## Unlookup: Holes Filled and Theorems Proved

The baseline unlookup reruns the lookup, which is correct on every input, so in particular on
`unlookupValidInputs`. It does not use measurement.
-/

namespace MbuImpl

open Operator Matrix QProg Function TableLookupSteps TableLookupImpl HermitianMat
open scoped Matrix ComplexOrder MatrixOrder

theorem mbu_conj_add_conj_eq {d : ℕ} (A : HermitianMat (Fin d) ℂ)
    (B₀ B₁ : Matrix (Fin d) (Fin d) ℂ) :
    A.conj B₀ᴴ + A.conj B₁ᴴ =
      A.conj (sqrtHalf • (B₀ + B₁))ᴴ + A.conj (sqrtHalf • (B₀ - B₁))ᴴ := by
  ext1
  have hs : star sqrtHalf = sqrtHalf := Complex.conj_ofReal _
  simp only [HermitianMat.mat_add, conj_apply_mat, conjTranspose_conjTranspose,
    conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, conjTranspose_add,
    conjTranspose_sub, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub]
  match_scalars <;> first | ring1 | linear_combination (-2 : ℂ) * sqrtHalf_mul_sqrtHalf

theorem lowerKraus_measure_qIf2 {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] (v : Var)
    (ℳ : Measurement d 2) {F G : QProg Var d} {R_F R_G : Matrix (Fin d) (Fin d) ℂ}
    (hF : LowerKraus F R_F) (hG : LowerKraus G R_G) :
    LowerKraus ((QProg.qMeasure v ℳ).qSeq (.qIf (fun σ ↦ σ v = 1) F G))
      (sqrtHalf • (R_G * ℳ.1 0 + R_F * ℳ.1 1)) := by
  intro A σ
  have hwp : (wp ((QProg.qMeasure v ℳ).qSeq (.qIf (fun σ ↦ σ v = 1) F G)) (fun _ ↦ A) σ).1 =
      (wp G (fun _ ↦ A) (Store.subst σ v 0)).1.conj (ℳ.1 0)ᴴ +
        (wp F (fun _ ↦ A) (Store.subst σ v 1)).1.conj (ℳ.1 1)ᴴ := by
    simp only [wp, CQAssertion.qMeasure_coe, Fin.sum_univ_two]
    simp [Store.subst]
  rw [hwp]
  calc A.1.conj (sqrtHalf • (R_G * ℳ.1 0 + R_F * ℳ.1 1))ᴴ
      ≤ A.1.conj (sqrtHalf • (R_G * ℳ.1 0 + R_F * ℳ.1 1))ᴴ +
          A.1.conj (sqrtHalf • (R_G * ℳ.1 0 - R_F * ℳ.1 1))ᴴ :=
        le_add_of_nonneg_right (conj_nonneg _ A.2.1)
    _ = (A.1.conj R_Gᴴ).conj (ℳ.1 0)ᴴ + (A.1.conj R_Fᴴ).conj (ℳ.1 1)ᴴ := by
        rw [← mbu_conj_add_conj_eq]
        simp only [conj_conj, conjTranspose_mul]
    _ ≤ _ := add_le_add (conj_mono (hG A _)) (conj_mono (hF A _))

theorem lowerKraus_measure_singleton_qIf2 {Var : Type} {n : ℕ} [DecidableEq Var] [NeZero (2 ^ n)]
    (v : Var) (t : Wire n) {F G : QProg Var (2 ^ n)}
    {R_F R_G : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hF : LowerKraus F R_F) (hG : LowerKraus G R_G) :
    LowerKraus ((QProg.measureRegister v (QRegister.singleton t)).qSeq
        (.qIf (fun σ ↦ σ v = 1) F G))
      (sqrtHalf • (R_G * (QRegister.singleton t).basisOutcomeProjector 0 +
        R_F * (QRegister.singleton t).basisOutcomeProjector 1)) :=
  lowerKraus_measure_qIf2 v _ hF hG

end MbuImpl

namespace MbuImpl

open Operator Matrix QProg Function TableLookupSteps TableLookupImpl HermitianMat
open scoped Matrix ComplexOrder MatrixOrder

variable {n : ℕ} {w : ℕ}

/-- The measurement tree: for each listed target wire in turn, `H`, measure, and on outcome `1`
reset the wire with `X` and continue with the mask extended by that wire; on outcome `0`
continue with the same mask. At the leaf the phase circuit `leaf r` runs. -/
def mbuTree (v : Var) (T : Fin w → Wire n) (leaf : (Fin w → ZMod 2) → DynamicCircuit Var n) :
    List (Fin w) → (Fin w → ZMod 2) → DynamicCircuit Var n
  | [], r => leaf r
  | i :: is, r =>
    .seq (.circuit (Circuit.H (T i))) (.seq (.measure v (QRegister.singleton (T i)))
      (.qIf (fun σ ↦ σ v = 1)
        (.seq (.circuit (Circuit.X (T i)))
          (mbuTree v T leaf is (fun j ↦ r j + if j = i then 1 else 0)))
        (mbuTree v T leaf is r)))

/-- Set the listed target wires to `0`. -/
def zeroL (T : Fin w → Wire n) : List (Fin w) → BitAssignment n → BitAssignment n
  | [], β => β
  | i :: is, β => zeroL T is (update β (T i) 0)

theorem sum_mask_step (r : Fin w → ZMod 2) (i : Fin w) (d : Fin w → ZMod 2) :
    ∑ j, (r j + if j = i then 1 else 0) * d j = ∑ j, r j * d j + d i := by
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem mbuTree_kraus [DecidableEq Var] [NeZero (2 ^ n)] (v : Var) (T : Fin w → Wire n)
    (leaf : (Fin w → ZMod 2) → DynamicCircuit Var n)
    (dd : Fin w → BitAssignment n → ZMod 2) (Good : BitAssignment n → Prop)
    (hT : Function.Injective T)
    (hGood : ∀ γ i a, Good γ → Good (update γ (T i) a))
    (hdd : ∀ γ i j a, dd j (update γ (T i) a) = dd j γ)
    (hleaf : ∀ r, ∃ L, LowerKraus (leaf r).compile L ∧ ∀ γ, Good γ →
        L.mulVec (ket γ) = bitSign (∑ j, r j * dd j γ) • ket γ) :
    ∀ (is : List (Fin w)), is.Nodup → ∀ r, ∃ R, LowerKraus (mbuTree v T leaf is r).compile R ∧
      ∀ β, Good β → R.mulVec (ket β) =
        if (∀ i ∈ is, β (T i) = dd i β) then
          bitSign (∑ j, r j * dd j β) • ket (zeroL T is β) else 0 := by
  intro is
  induction is with
  | nil =>
    intro _ r
    obtain ⟨L, hK, hL⟩ := hleaf r
    refine ⟨L, hK, fun β hβ ↦ ?_⟩
    simp [zeroL, hL β hβ]
  | cons i is ih =>
    intro hnd r
    have hnd' := List.nodup_cons.mp hnd
    obtain ⟨R_G, hKG, hRG⟩ := ih hnd'.2 r
    obtain ⟨R_S, hKS, hRS⟩ := ih hnd'.2 (fun j ↦ r j + if j = i then 1 else 0)
    refine ⟨(sqrtHalf • (R_G * (QRegister.singleton (T i)).basisOutcomeProjector 0 +
        (R_S * (Circuit.X (T i)).eval.1) * (QRegister.singleton (T i)).basisOutcomeProjector 1)) *
        (Circuit.H (T i)).eval.1, ?_, ?_⟩
    · exact (lowerKraus_circuit (Circuit.H (T i))).qSeq
        (lowerKraus_measure_singleton_qIf2 v (T i)
          ((lowerKraus_circuit (Circuit.X (T i))).qSeq hKS) hKG)
    · intro β hβ
      have hne : ∀ j ∈ is, T j ≠ T i := fun j hj h ↦ hnd'.1 (hT h ▸ hj)
      have hβ0 : Good (update β (T i) 0) := hGood _ _ _ hβ
      have hH := ket_H (T i) β
      have hX : (Circuit.X (T i)).eval.1.mulVec (ket (update β (T i) 1)) =
          ket (update β (T i) 0) := by
        rw [ket_X, update_self, update_idem, one_add_one_zmod2]
      have hQ : (∀ j ∈ is, (update β (T i) 0) (T j) = dd j (update β (T i) 0)) ↔
          (∀ j ∈ is, β (T j) = dd j β) := by
        refine forall₂_congr fun j hj ↦ ?_
        rw [update_of_ne (hne j hj), hdd]
      have hsum : ∑ j, (r j + if j = i then 1 else 0) * dd j (update β (T i) 0) =
          ∑ j, r j * dd j β + dd i β := by
        simp only [hdd]
        exact sum_mask_step r i (fun j ↦ dd j β)
      have hsumr : ∑ j, r j * dd j (update β (T i) 0) = ∑ j, r j * dd j β := by
        simp only [hdd]
      have hRG0 := hRG _ hβ0
      have hRS0 := hRS _ hβ0
      rw [hsum] at hRS0
      rw [hsumr] at hRG0
      simp only [← Matrix.mulVec_mulVec, hH, Matrix.mulVec_smul, Matrix.smul_mulVec,
        Matrix.add_mulVec, Matrix.mulVec_add, ket_projector_zero, ket_projector_one, update_self,
        hX, ↓reduceIte, one_ne_zero, zero_ne_one, Matrix.mulVec_zero, add_zero, zero_add]
      by_cases hq : ∀ j ∈ is, β (T j) = dd j β
      · rw [if_pos (hQ.mpr hq)] at hRG0 hRS0
        rw [hRG0, hRS0, bitSign_add, mul_comm (bitSign (∑ j, r j * dd j β)) (bitSign (dd i β)),
          mul_smul]
        rw [Step.unand_scalar]
        simp only [List.mem_cons, forall_eq_or_imp, hq, and_true, zeroL]
        by_cases hb : β (T i) = dd i β <;> simp [hb] <;> (intro x hx h; exact absurd (hq x hx) h)
      · rw [if_neg (fun h ↦ hq (hQ.mp h))] at hRG0 hRS0
        rw [hRG0, hRS0]
        simp only [List.mem_cons, forall_eq_or_imp, hq, and_false, smul_zero, add_zero]
        simp
end MbuImpl

namespace MbuImpl

open Operator Matrix QProg Function TableLookupSteps TableLookupImpl SelectSwapImpl HermitianMat
open scoped Matrix ComplexOrder MatrixOrder

variable {n : ℕ}

/-- Compute half of the width-1 phase lookup. -/
def leafC (m s : ℕ) (f : ℕ → ℕ) (rXl : QRegister s n) (rXh rW : QRegister (m - s) n)
    (rD : QRegister (2 ^ s * 1) n) (ci : Wire n) : List (Step n) :=
  lookupSteps (2 ^ s * 1) rD (m - s) none rXh rW (wideTab s 1 f) ++
    swapTree ci 1 (dataBlock s 1 rD) s rXl

/-- Uncompute half of the width-1 phase lookup. -/
def leafU (m s : ℕ) (f : ℕ → ℕ) (rXl : QRegister s n) (rXh rW : QRegister (m - s) n)
    (rD : QRegister (2 ^ s * 1) n) (ci : Wire n) : List (Step n) :=
  (swapTree ci 1 (dataBlock s 1 rD) s rXl).reverse.map Step.inv ++
    lookupSteps (2 ^ s * 1) rD (m - s) none rXh rW (wideTab s 1 f)

theorem runList_leaf (m s : ℕ) (f : ℕ → ℕ) (rXl : QRegister s n) (rXh rW : QRegister (m - s) n)
    (rD : QRegister (2 ^ s * 1) n) (ci : Wire n)
    (hDl : rD.DisjointWires rXl) (hDh : rD.DisjointWires rXh) (hDW : rD.DisjointWires rW)
    (hhW : rXh.DisjointWires rW) (hiD : ci ∉ Set.range rD.wires)
    (hiXl : ci ∉ Set.range rXl.wires) (β : BitAssignment n)
    (hD : ∀ i, β (rD i) = 0) (hW : ∀ i, β (rW i) = 0) (hci : β ci = 0) :
    ∃ β2, runList (leafC m s f rXl rXh rW rD ci) β = some β2 ∧
      β2 (dataBlock s 1 rD 0 0) =
        tableBits 1 f ((localIdx rXl β : ℕ) + 2 ^ s * (localIdx rXh β : ℕ)) 0 ∧
      runList (leafU m s f rXl rXh rW rD ci) β2 = some β := by
  set B := dataBlock s 1 rD with hBdef
  set S := swapTree ci 1 B s rXl with hS
  have hnB : ∀ {v}, v ∉ Set.range rD.wires → ∀ l, v ∉ Set.range (B l).wires :=
    fun hv _ ↦ not_mem_slice hv _ _ _
  have hlook := fun β' ↦ runList_lookupSteps (2 ^ s * 1) rD (m - s) none rXh rW
    (wideTab s 1 f) hhW
    (QRegister.disjoint_comm.mp hDh) (QRegister.disjoint_comm.mp hDW)
    (fun _ ↦ ctrlNe_none _) (fun _ ↦ ctrlNe_none _) (fun _ ↦ ctrlNe_none _) β'
  set β1 := writeReg β rD (wideTab s 1 f (localIdx rXh β)) with hβ1
  have h1 : runList (lookupSteps (2 ^ s * 1) rD (m - s) none rXh rW (wideTab s 1 f)) β =
      some β1 := by
    rw [hlook β hW]
    simp only [hD, ctrlVal, zero_add, one_mul]
    rfl
  have hb1 : ∀ v, v ∉ Set.range rD.wires → β1 v = β v := fun v hv ↦
    writeReg_apply_of_not_mem _ _ _ _ hv
  obtain ⟨β2, h2, hfr2_B, h2B⟩ := runList_swapTree ci 1 B s rXl
    (fun l l' hl hl' h ↦ dataBlock_disjoint s 1 rD hl hl' h)
    (fun j ↦ hnB (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDl) j))
    hiXl (hnB hiD) β1 (by rw [hb1 _ hiD, hci])
  refine ⟨β2, ?_, ?_, ?_⟩
  · rw [leafC, runList_append, h1, Option.bind_some, ← hS, h2]
  · have hl := (localIdx rXl β).isLt
    rw [h2B, localIdx_writeReg_of_disjoint _ _ _ hDl, hβ1,
      writeReg_wideTab_dataBlock _ _ _ _ _ _ _ hl]
  · rw [leafU, runList_append, runList_inv (swapTree_noUnxor ci 1 B s rXl) h2, Option.bind_some,
      hlook _ (fun i ↦ by
        rw [hb1 _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDW) i), hW])]
    simp only [hβ1, localIdx_writeReg_of_disjoint _ _ _ hDh, writeReg_apply_reg, ctrlVal,
      one_mul, CharTwo.add_self_eq_zero]
    rw [writeReg_writeReg,
      show (fun _ : Fin (2 ^ s * 1) ↦ (0 : ZMod 2)) = fun i ↦ β (rD i) from
        funext fun i ↦ (hD i).symm, writeReg_self]

end MbuImpl

namespace MbuImpl

open Operator Matrix QProg Function TableLookupSteps TableLookupImpl SelectSwapImpl HermitianMat
open scoped Matrix ComplexOrder MatrixOrder

variable {n : ℕ} {w : ℕ}

/-- The width-1 phase lookup: compute, `Z` on the single data bit, uncompute. -/
def leafCirc (m s : ℕ) (f : ℕ → ℕ) (rXl : QRegister s n) (rXh rW : QRegister (m - s) n)
    (rD : QRegister (2 ^ s * 1) n) (ci : Wire n) : DynamicCircuit Var n :=
  .seq (compileList (Var.v 0) (leafC m s f rXl rXh rW rD ci))
    (.seq (.circuit (Circuit.Z (dataBlock s 1 rD 0 0)))
      (compileList (Var.v 0) (leafU m s f rXl rXh rW rD ci)))

theorem leafCirc_kraus [NeZero (2 ^ n)] (m s : ℕ) (f : ℕ → ℕ) (rXl : QRegister s n)
    (rXh rW : QRegister (m - s) n) (rD : QRegister (2 ^ s * 1) n) (ci : Wire n)
    (hDl : rD.DisjointWires rXl) (hDh : rD.DisjointWires rXh) (hDW : rD.DisjointWires rW)
    (hhW : rXh.DisjointWires rW) (hiD : ci ∉ Set.range rD.wires)
    (hiXl : ci ∉ Set.range rXl.wires) :
    ∃ L, LowerKraus (leafCirc m s f rXl rXh rW rD ci).compile L ∧
      ∀ β : BitAssignment n, (∀ i, β (rD i) = 0) → (∀ i, β (rW i) = 0) → β ci = 0 →
        L.mulVec (ket β) = bitSign (tableBits 1 f
          ((localIdx rXl β : ℕ) + 2 ^ s * (localIdx rXh β : ℕ)) 0) • ket β := by
  obtain ⟨RC, hKC, hRC, -⟩ := exists_lowerKraus_compileList (Var.v 0)
    (leafC m s f rXl rXh rW rD ci)
  obtain ⟨RU, hKU, hRU, -⟩ := exists_lowerKraus_compileList (Var.v 0)
    (leafU m s f rXl rXh rW rD ci)
  refine ⟨RU * (Circuit.Z (dataBlock s 1 rD 0 0)).eval.1 * RC, ?_, ?_⟩
  · exact hKC.qSeq ((lowerKraus_circuit _).qSeq hKU)
  · intro β hD hW hci
    obtain ⟨β2, h1, h2, h3⟩ := runList_leaf m s f rXl rXh rW rD ci hDl hDh hDW hhW hiD hiXl β
      hD hW hci
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hRC _ _ h1, ket_Z, h2,
      Matrix.mulVec_smul, hRU _ _ h3]

theorem leafCirc_count_T (m s : ℕ) (hs : s ≤ m) (f : ℕ → ℕ) (rXl : QRegister s n)
    (rXh rW : QRegister (m - s) n) (rD : QRegister (2 ^ s * 1) n) (ci : Wire n) :
    (leafCirc m s f rXl rXh rW rD ci).count PrimitiveGate.T ≤ ssT m 1 s := by
  have hC := count_T_compileList (Var.v 0) (leafC m s f rXl rXh rW rD ci)
  have hU := count_T_compileList (Var.v 0) (leafU m s f rXl rXh rW rD ci)
  have h1 : ac (lookupSteps (2 ^ s * 1) rD (m - s) none rXh rW (wideTab s 1 f)) ≤
      2 ^ (m - s) - 1 := andCount_lookupSteps _ _ _ _ _ _ _
  have h2 := ac_swapTree ci 1 (dataBlock s 1 rD) s rXl
  have h3 : ac ((swapTree ci 1 (dataBlock s 1 rD) s rXl).reverse.map Step.inv) + 1 =
      2 ^ s * 1 := aci_swapTree ci 1 (dataBlock s 1 rD) s rXl
  have eC : ((leafC m s f rXl rXh rW rD ci).map Step.andCount).sum =
      ac (lookupSteps (2 ^ s * 1) rD (m - s) none rXh rW (wideTab s 1 f)) +
        ac (swapTree ci 1 (dataBlock s 1 rD) s rXl) := ac_append _ _
  have eU : ((leafU m s f rXl rXh rW rD ci).map Step.andCount).sum =
      ac ((swapTree ci 1 (dataBlock s 1 rD) s rXl).reverse.map Step.inv) +
        ac (lookupSteps (2 ^ s * 1) rD (m - s) none rXh rW (wideTab s 1 f)) := ac_append _ _
  have h4 : 8 * (2 ^ s - 1) * 1 + 8 = 8 * (2 ^ s * 1) := by
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ s = k + 1 := ⟨2 ^ s - 1, by have := @Nat.one_le_two_pow s; omega⟩
    rw [hk, Nat.add_sub_cancel]
    ring
  have hz : (Circuit.Z (dataBlock s 1 rD 0 0)).count PrimitiveGate.T = 0 := by simp
  simp only [leafCirc, DynamicCircuit.count, hz] at *
  unfold ssT
  rw [eC] at hC
  rw [eU] at hU
  omega

theorem leafCirc_count_TOFF (m s : ℕ) (f : ℕ → ℕ) (rXl : QRegister s n)
    (rXh rW : QRegister (m - s) n) (rD : QRegister (2 ^ s * 1) n) (ci : Wire n) :
    (leafCirc m s f rXl rXh rW rD ci).count PrimitiveGate.TOFF = 0 := by
  have hz : (Circuit.Z (dataBlock s 1 rD 0 0)).count PrimitiveGate.TOFF = 0 := by simp
  simp only [leafCirc, DynamicCircuit.count, hz, count_TOFF_compileList]

theorem mbuTree_count (v : Var) (T : Fin w → Wire n)
    (leaf : (Fin w → ZMod 2) → DynamicCircuit Var n) {k : ℕ} (g : PrimitiveGate k) (b : ℕ)
    (hH : ∀ q : Wire n, (Circuit.H q).count g = 0) (hX : ∀ q : Wire n, (Circuit.X q).count g = 0)
    (hl : ∀ r, (leaf r).count g ≤ b) :
    ∀ (is : List (Fin w)) r, (mbuTree v T leaf is r).count g ≤ b := by
  intro is
  induction is with
  | nil => intro r; exact hl r
  | cons i is ih =>
    intro r
    simp only [mbuTree, DynamicCircuit.count, hH, hX, zero_add]
    exact max_le (by simpa using ih (fun j ↦ r j + if j = i then 1 else 0)) (ih r)

end MbuImpl

namespace MbuImpl

open Operator Matrix QProg Function TableLookupSteps TableLookupImpl SelectSwapImpl HermitianMat
open scoped Matrix ComplexOrder MatrixOrder

variable {n : ℕ}

theorem zeroL_apply {w : ℕ} (T : Fin w → Wire n) :
    ∀ (is : List (Fin w)) (β : BitAssignment n) (v : Wire n),
      zeroL T is β v = if ∃ i ∈ is, T i = v then 0 else β v := by
  intro is
  induction is with
  | nil => intro β v; simp [zeroL]
  | cons i is ih =>
    intro β v
    rw [zeroL, ih]
    by_cases h : ∃ j ∈ is, T j = v
    · rw [if_pos h, if_pos (by obtain ⟨j, hj, e⟩ := h; exact ⟨j, List.mem_cons_of_mem _ hj, e⟩)]
    · rw [if_neg h]
      by_cases hv : T i = v
      · rw [if_pos ⟨i, List.mem_cons_self .., hv⟩, ← hv, update_self]
      · rw [if_neg (by
          rintro ⟨j, hj, e⟩
          rcases List.mem_cons.mp hj with rfl | hj
          · exact hv e
          · exact h ⟨j, hj, e⟩), update_of_ne (fun e ↦ hv e.symm)]

theorem zeroL_finRange {p : LookupParams} (rData : QRegister (p.m + p.w) n) (β : BitAssignment n) :
    zeroL (fun i ↦ targetReg p rData i) (List.finRange p.w) β =
      writeReg β (targetReg p rData) (fun _ ↦ 0) := by
  funext v
  rw [zeroL_apply]
  by_cases hv : v ∈ Set.range (targetReg p rData).wires
  · obtain ⟨i, rfl⟩ := hv
    rw [if_pos ⟨i, List.mem_finRange _, rfl⟩]
    exact (writeReg_apply_reg β (targetReg p rData) (fun _ ↦ 0) i).symm
  · rw [writeReg_apply_of_not_mem _ _ _ _ hv, if_neg]
    rintro ⟨i, -, rfl⟩
    exact hv ⟨i, rfl⟩

theorem target_eq_of_valid {p : LookupParams} (data : LookupTable p)
    (rData : QRegister (p.m + p.w) n) (β : BitAssignment n)
    (hmem : localIdx rData β ∈ unlookupValidInputs data) (i : Fin p.w) :
    β (targetReg p rData i) = lookupWords data (localIdx (addrReg p rData) β) i := by
  set X := localIdx (addrReg p rData) β with hX
  set Y := localIdx (targetReg p rData) β with hY
  have hv : (localIdx rData β).val = Y.val + 2 ^ p.w * X.val :=
    localIdx_val_split rData p.w p.m (by omega) β
  have hx' : (splitBasisEquiv p.m p.w (localIdx rData β)).1 = X := by
    apply Fin.ext
    rw [splitBasisEquiv_fst_val, hv, Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt Y.isLt, zero_add]
  have hb' : (splitBasisEquiv p.m p.w (localIdx rData β)).2 = Y := by
    apply Fin.ext
    rw [splitBasisEquiv_snd_val, hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt Y.isLt]
  have h2 := hmem.2
  rw [hx', hb'] at h2
  have e : β (targetReg p rData i) = basisBits p.w Y i := by
    simp only [hY, localIdx, Equiv.apply_symm_apply]
  rw [e, h2, lookupWords, dif_pos X.isLt]

end MbuImpl

namespace MbuImpl

open Operator Matrix QProg Function TableLookupSteps TableLookupImpl SelectSwapImpl HermitianMat
open scoped Matrix ComplexOrder MatrixOrder

variable {n : ℕ}

/-- The one-bit table `x ↦ parity (r AND data(x))`, as a natural number. -/
def maskTab (p : LookupParams) (data : LookupTable p) (r : Fin p.w → ZMod 2) (x : ℕ) : ℕ :=
  (∑ j, r j * lookupWords data x j).val

theorem maskTab_bit (p : LookupParams) (data : LookupTable p) (r : Fin p.w → ZMod 2) (x : ℕ) :
    tableBits 1 (maskTab p data r) x 0 = ∑ j, r j * lookupWords data x j := by
  simp only [tableBits, maskTab, Fin.val_zero, _root_.pow_zero, Nat.div_one]
  rw [ZMod.natCast_mod, ZMod.natCast_zmod_val]

/-- The measurement-based unlookup. -/
def mbuProg (p : LookupParams) (s : ℕ) (hs : s ≤ p.m) (data : LookupTable p)
    (rData : QRegister (p.m + p.w) n) {N : ℕ} (rAnc : QRegister N n)
    (hN : 2 ^ s * 1 + (p.m - s) + 1 ≤ N) : DynamicCircuit Var n :=
  mbuTree (Var.v 0) (fun i ↦ targetReg p rData i)
    (fun r ↦ leafCirc p.m s (maskTab p data r) (rData.slice p.w s (by omega))
      (rData.slice (p.w + s) (p.m - s) (by omega))
      (rAnc.slice (2 ^ s * 1) (p.m - s) (by omega)) (rAnc.slice 0 (2 ^ s * 1) (by omega))
      (rAnc ⟨2 ^ s * 1 + (p.m - s), by omega⟩))
    (List.finRange p.w) (fun _ ↦ 0)

theorem mbuProg_realizes (p : LookupParams) (s : ℕ) (hs : s ≤ p.m) (data : LookupTable p)
    (rData : QRegister (p.m + p.w) n) {N : ℕ} (rAnc : QRegister N n)
    (hN : 2 ^ s * 1 + (p.m - s) + 1 ≤ N) (hd : rData.DisjointWires rAnc) :
    RealizesCleanSubroutineOnEncoding rData rAnc hd (unlookupValidInputs data)
      (tableXorPerm data.extend) (mbuProg p s hs data rData rAnc hN).compile := by
  haveI : NeZero (2 ^ n) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hDA : ∀ {a b : ℕ} (r : QRegister a (p.m + p.w)) (r' : QRegister b N),
      (rAnc.compose r').DisjointWires (rData.compose r) := fun _ _ ↦
    QRegister.disjoint_comm.mp ((hd.compose_left _).compose_right _)
  have hTA : (targetReg p rData).DisjointWires rAnc := hd.compose_left _
  have hYX : (targetReg p rData).DisjointWires (addrReg p rData) :=
    rData.slice_disjoint_of_le 0 p.w p.w p.m _ _ (by omega)
  have hx : ∀ γ : BitAssignment n, (localIdx (addrReg p rData) γ : ℕ) =
      (localIdx (rData.slice p.w s (by omega)) γ : ℕ) +
        2 ^ s * (localIdx (rData.slice (p.w + s) (p.m - s) (by omega)) γ : ℕ) := fun γ ↦ by
    rw [localIdx_val_split (addrReg p rData) s (p.m - s) (by omega)]
    simp only [localIdx_slice_slice, add_zero]
  obtain ⟨R, hK, hR⟩ := mbuTree_kraus (Var.v 0) (fun i ↦ targetReg p rData i)
    (fun r ↦ leafCirc p.m s (maskTab p data r) (rData.slice p.w s (by omega))
      (rData.slice (p.w + s) (p.m - s) (by omega))
      (rAnc.slice (2 ^ s * 1) (p.m - s) (by omega)) (rAnc.slice 0 (2 ^ s * 1) (by omega))
      (rAnc ⟨2 ^ s * 1 + (p.m - s), by omega⟩))
    (fun i γ ↦ lookupWords data (localIdx (addrReg p rData) γ) i)
    (fun γ ↦ localIdx rAnc γ = 0)
    (fun i j h ↦ (targetReg p rData).wires.injective h)
    (fun γ i a h ↦ by
      rw [localIdx_update_of_not_mem rAnc γ (not_mem_of_disjoint hTA i) a]
      exact h)
    (fun γ i j a ↦ by
      simp only [localIdx_update_of_not_mem (addrReg p rData) γ (not_mem_of_disjoint hYX i) a])
    (fun r ↦ by
      obtain ⟨L, hL, hLk⟩ := leafCirc_kraus p.m s (maskTab p data r)
        (rData.slice p.w s (by omega)) (rData.slice (p.w + s) (p.m - s) (by omega))
        (rAnc.slice (2 ^ s * 1) (p.m - s) (by omega)) (rAnc.slice 0 (2 ^ s * 1) (by omega))
        (rAnc ⟨2 ^ s * 1 + (p.m - s), by omega⟩)
        (hDA _ _) (hDA _ _)
        (QRegister.slice_disjoint_of_le rAnc _ _ _ _ (by omega) (by omega) (by omega))
        (QRegister.disjoint_comm.mp (hDA _ _))
        (apply_not_mem_slice rAnc _ 0 _ (by omega) (Or.inr (by simp)))
        (fun ⟨_, h⟩ ↦ hd.ne _ _ h)
      refine ⟨L, hL, fun γ hγ ↦ ?_⟩
      have hcl := eq_zero_of_localIdx_eq_zero rAnc γ hγ
      rw [hLk γ (fun _ ↦ hcl _) (fun _ ↦ hcl _) (hcl _), ← hx γ, maskTab_bit])
    (List.finRange p.w) (List.nodup_finRange _) (fun _ ↦ 0)
  refine realizesOnEncoding_of_lowerKraus rData rAnc hd _ _ hK fun β h0 hmem ↦ ?_
  rw [hR β h0, if_pos (fun i _ ↦ target_eq_of_valid data rData β hmem i)]
  simp only [zero_mul, Finset.sum_const_zero, bitSign, if_true, one_smul]
  rw [zeroL_finRange, ← target_xor_eq data rData β]
  congr 2
  funext i
  rw [target_eq_of_valid data rData β hmem i, CharTwo.add_self_eq_zero]

theorem mbuProg_count_T (p : LookupParams) (s : ℕ) (hs : s ≤ p.m) (data : LookupTable p)
    (rData : QRegister (p.m + p.w) n) {N : ℕ} (rAnc : QRegister N n)
    (hN : 2 ^ s * 1 + (p.m - s) + 1 ≤ N) :
    (mbuProg p s hs data rData rAnc hN).count PrimitiveGate.T ≤ ssT p.m 1 s :=
  mbuTree_count _ _ _ _ _ (fun q ↦ by simp) (fun q ↦ by simp)
    (fun r ↦ leafCirc_count_T _ _ hs _ _ _ _ _ _) _ _

theorem mbuProg_count_TOFF (p : LookupParams) (s : ℕ) (hs : s ≤ p.m) (data : LookupTable p)
    (rData : QRegister (p.m + p.w) n) {N : ℕ} (rAnc : QRegister N n)
    (hN : 2 ^ s * 1 + (p.m - s) + 1 ≤ N) :
    (mbuProg p s hs data rData rAnc hN).count PrimitiveGate.TOFF = 0 := by
  have := mbuTree_count (Var.v 0) (fun i ↦ targetReg p rData i)
    (fun r ↦ leafCirc p.m s (maskTab p data r) (rData.slice p.w s (by omega))
      (rData.slice (p.w + s) (p.m - s) (by omega))
      (rAnc.slice (2 ^ s * 1) (p.m - s) (by omega)) (rAnc.slice 0 (2 ^ s * 1) (by omega))
      (rAnc ⟨2 ^ s * 1 + (p.m - s), by omega⟩)) PrimitiveGate.TOFF 0
    (fun q ↦ by simp) (fun q ↦ by simp)
    (fun r ↦ (leafCirc_count_TOFF _ _ _ _ _ _ _ _).le) (List.finRange p.w) (fun _ ↦ 0)
  exact Nat.le_zero.mp this

end MbuImpl

namespace UuImpl

/-- Swap depth in `0..m` minimizing `T count * (m + w + ancillas)` of the measurement-based
unlookup (ties to the smaller `s`). -/
def uuS (m w : ℕ) : ℕ :=
  (List.range (m + 1)).foldl
    (fun b s ↦
      if SelectSwapImpl.ssT m 1 s * (m + w + SelectSwapImpl.ssA m 1 s) <
          SelectSwapImpl.ssT m 1 b * (m + w + SelectSwapImpl.ssA m 1 b) then s else b) 0

/-- The measurement-based unlookup at depth `uuS m w` beats the unary one on spacetime. -/
abbrev uuCond (m w : ℕ) : Prop :=
  uuS m w ≤ m ∧
    SelectSwapImpl.ssT m 1 (uuS m w) * (m + w + SelectSwapImpl.ssA m 1 (uuS m w)) <
      4 * (2 ^ m - 1) * (m + w + m)

end UuImpl

/-- Number of clean ancilla qubits `qromUnlookupProgram` uses for sizes `p`: the
measurement-based unlookup's `2 ^ s + (m - s) + 1` at the spacetime-optimal swap depth `s` when
that beats the unary unlookup, and `m` otherwise. -/
def qromUnlookupAncillas (p : LookupParams) : ℕ :=
  if UuImpl.uuCond p.m p.w then
    SelectSwapImpl.ssA p.m 1 (UuImpl.uuS p.m p.w)
  else p.m

/-- Unlookup circuit for table `data` on the `p.m + p.w` data wires `rData` (`p.w` target wires
followed by `p.m` address wires) and `qromUnlookupAncillas p` clean ancilla wires `rAnc`. When
the measurement-based variant is cheaper it measures the `p.w` target wires in the Hadamard basis
and applies a width-one phase lookup per outcome pattern; otherwise it reruns the lookup. -/
def qromUnlookupProgram {n : ℕ} (p : LookupParams) (data : LookupTable p)
    (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromUnlookupAncillas p) n) : DynamicCircuit Var n :=
  if h : UuImpl.uuCond p.m p.w then
    MbuImpl.mbuProg p (UuImpl.uuS p.m p.w) h.1 data rData rAnc (le_of_eq (if_pos h).symm)
  else
    qromLookupProgram p data rData (SelectSwapImpl.castReg (if_neg h) rAnc)

/-- For valid sizes and every table, `qromUnlookupProgram` realizes
`|x⟩|data(x)⟩ ↦ |x⟩|0⟩` on every address `x < L`, as an exact clean subroutine across all
disjoint register placements. Inputs whose target differs from `data(x)` are unconstrained. -/
theorem qromUnlookup_correctness (p : LookupParams) (hp : p.Valid) (data : LookupTable p)
    {n : ℕ} (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromUnlookupAncillas p) n) (hdisj : rData.DisjointWires rAnc) :
    RealizesCleanSubroutineOnEncoding rData rAnc hdisj (unlookupValidInputs data)
      (tableXorPerm data.extend) (qromUnlookupProgram p data rData rAnc).compile := by
  by_cases h : UuImpl.uuCond p.m p.w
  · unfold qromUnlookupProgram
    rw [dif_pos h]
    exact MbuImpl.mbuProg_realizes p _ h.1 data rData rAnc _ hdisj
  · unfold qromUnlookupProgram
    rw [dif_neg h]
    exact SelectSwapImpl.castReg_realizes p data rData (if_neg h) rAnc hdisj _

/-- Claimed `T` count of the unlookup, as a function of the sizes. -/
def qromUnlookupTCost (p : LookupParams) : ℕ :=
  if UuImpl.uuCond p.m p.w then SelectSwapImpl.ssT p.m 1 (UuImpl.uuS p.m p.w)
  else 4 * (2 ^ p.m - 1)

/-- For valid sizes, every table and every placement, the unlookup uses no `TOFF` gates and at
most `qromUnlookupTCost p` `T` gates. Classically controlled branches count as the larger
branch, so this bounds every measurement record. -/
theorem qromUnlookup_t_cost (p : LookupParams) (hp : p.Valid) (data : LookupTable p)
    {n : ℕ} (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromUnlookupAncillas p) n) :
    (qromUnlookupProgram p data rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (qromUnlookupProgram p data rData rAnc).count PrimitiveGate.T ≤ qromUnlookupTCost p := by
  by_cases h : UuImpl.uuCond p.m p.w
  · unfold qromUnlookupProgram qromUnlookupTCost
    rw [dif_pos h, if_pos h]
    exact ⟨MbuImpl.mbuProg_count_TOFF p _ h.1 data rData rAnc _,
      MbuImpl.mbuProg_count_T p _ h.1 data rData rAnc _⟩
  · unfold qromUnlookupProgram
    rw [dif_neg h]
    exact ⟨lookup_count_TOFF (Var.v 0) p data rData _,
      (lookup_count_T (Var.v 0) p data rData _).trans (le_of_eq (if_neg h).symm)⟩

/-- Claimed spacetime cost `T count * (m + w + ancillas)` of the unlookup, as a function of the
sizes. -/
def qromUnlookupSpacetimeCost (p : LookupParams) : ℕ :=
  if UuImpl.uuCond p.m p.w then
    SelectSwapImpl.ssT p.m 1 (UuImpl.uuS p.m p.w) *
      (p.m + p.w + SelectSwapImpl.ssA p.m 1 (UuImpl.uuS p.m p.w))
  else 4 * (2 ^ p.m - 1) * (p.m + p.w + p.m)

/-- For valid sizes, every table and every placement, the unlookup uses no `TOFF` gates and has
`T count * (p.m + p.w + qromUnlookupAncillas p) ≤ qromUnlookupSpacetimeCost p`. -/
theorem qromUnlookup_spacetime_cost (p : LookupParams) (hp : p.Valid) (data : LookupTable p)
    {n : ℕ} (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromUnlookupAncillas p) n) :
    (qromUnlookupProgram p data rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (qromUnlookupProgram p data rData rAnc).count PrimitiveGate.T *
          (p.m + p.w + qromUnlookupAncillas p) ≤ qromUnlookupSpacetimeCost p := by
  obtain ⟨h1, h2⟩ := qromUnlookup_t_cost p hp data rData rAnc
  refine ⟨h1, ?_⟩
  by_cases h : UuImpl.uuCond p.m p.w
  · unfold qromUnlookupSpacetimeCost qromUnlookupAncillas
    rw [if_pos h, if_pos h]
    unfold qromUnlookupTCost at h2
    rw [if_pos h] at h2
    exact Nat.mul_le_mul_right _ h2
  · unfold qromUnlookupSpacetimeCost qromUnlookupAncillas
    rw [if_neg h, if_neg h]
    unfold qromUnlookupTCost at h2
    rw [if_neg h] at h2
    exact Nat.mul_le_mul_right _ h2

/-- Claimed spacetime cost bound for the unlookup at `LookupParams.l1024w32`:
`496 * (10 + 32 + 38) = 39680` (swap depth `5`). -/
def qromUnlookupL1024W32ConstCost : ℕ := 39680

/-- At `LookupParams.l1024w32`, for every table and every placement, the unlookup uses no `TOFF`
gates and has `T count * (m + w + qromUnlookupAncillas) ≤ qromUnlookupL1024W32ConstCost`. -/
theorem qromUnlookup_l1024w32_const_cost (data : LookupTable .l1024w32) {n : ℕ}
    (rData : QRegister (LookupParams.l1024w32.m + LookupParams.l1024w32.w) n)
    (rAnc : QRegister (qromUnlookupAncillas .l1024w32) n) :
    (qromUnlookupProgram .l1024w32 data rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (qromUnlookupProgram .l1024w32 data rData rAnc).count PrimitiveGate.T *
          (LookupParams.l1024w32.m + LookupParams.l1024w32.w + qromUnlookupAncillas .l1024w32) ≤
        qromUnlookupL1024W32ConstCost := by
  have hv : LookupParams.Valid .l1024w32 := by
    unfold LookupParams.Valid
    decide
  obtain ⟨h1, h2⟩ := qromUnlookup_t_cost .l1024w32 hv data rData rAnc
  have hc : qromUnlookupTCost .l1024w32 = 496 := by decide
  have ha : qromUnlookupAncillas .l1024w32 = 38 := by decide
  refine ⟨h1, ?_⟩
  calc _ ≤ qromUnlookupTCost .l1024w32 * _ := Nat.mul_le_mul_right _ h2
    _ ≤ _ := by rw [hc, ha]; decide

/-!
## Lookup and Unlookup with a Clean-Ancilla Budget

Published lookup records trade `T` gates for clean ancillas: select-swap lookup (Low,
Kliuchnikov and Schaeffer, arXiv:1812.00954; Berry et al., arXiv:1902.02134, Appendix A) loads
`k` words at a time into `k w` extra qubits and uses roughly `L / k + k w` Toffolis instead of
`L - 1`. That trade-off is a curve, not one number: it loses to unary iteration on
`T count * qubits`, so the spacetime theorems above cannot express it. The specs below take the
ancilla budget `a` as a size parameter. The ancilla count may be anything up to `a`, and the
claimed `T` count is a function of `(L, m, w, a)`, so a record is a point on the curve.
Correctness is the same as for the unbudgeted specs.
-/

/-- Sizes of a table lookup together with a clean-ancilla budget `a`. -/
structure BudgetLookupParams extends LookupParams where
  /-- Clean-ancilla budget `a`. -/
  a : ℕ

/-- The sizes are valid and the budget is at least `m`, which unary iteration needs. -/
def BudgetLookupParams.Valid (p : BudgetLookupParams) : Prop :=
  p.toLookupParams.Valid ∧ p.m ≤ p.a

/-- Pinned size and budget for single-number records: `L = 1024` entries of `w = 32` bits,
`m = 10`, and at most `a = 256` clean ancillas (room for `k = 4` words plus address workspace,
or `k = 8` words packed tightly). -/
abbrev BudgetLookupParams.l1024w32a256 : BudgetLookupParams where
  L := 1024
  m := 10
  w := 32
  a := 256


namespace MbuImpl

open Operator Matrix QProg Function TableLookupSteps TableLookupImpl SelectSwapImpl HermitianMat
open scoped Matrix ComplexOrder MatrixOrder

variable {n : ℕ}

/-- The previous (select-swap) unlookup ancilla count. -/
def oldAnc (p : BudgetLookupParams) : ℕ := SelectSwapImpl.ssAnc p.m p.w p.a

/-- The previous (select-swap) unlookup program. -/
def oldProg (p : BudgetLookupParams)
    (data : LookupTable p.toLookupParams) (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (oldAnc p) n) : DynamicCircuit Var n :=
  if h : SelectSwapImpl.ssCond p.m p.w p.a then
    compileList (Var.v 0) (SelectSwapImpl.ssProgSteps p.toLookupParams
      (SelectSwapImpl.ssBest p.m p.w p.a) data rData rAnc
      (SelectSwapImpl.ssAnc_pos h).ge h.1)
  else
    qromLookupProgram p.toLookupParams data rData (SelectSwapImpl.castReg (SelectSwapImpl.ssAnc_neg h) rAnc)

/-- The previous unlookup `T` cost. -/
def oldTCost (m w a : ℕ) : ℕ :=
  if SelectSwapImpl.ssCond m w a then
    SelectSwapImpl.ssT m w (SelectSwapImpl.ssBest m w a) else 4 * (2 ^ m - 1)

/-- Use the measurement-based unlookup. -/
def mbuCond (m w a : ℕ) : Prop :=
  ssBest m 1 a ≤ m ∧ ssA m 1 (ssBest m 1 a) ≤ a ∧
    ssT m 1 (ssBest m 1 a) < oldTCost m w a

instance (m w a : ℕ) : Decidable (mbuCond m w a) := by unfold mbuCond; infer_instance

theorem oldProg_realizes (p : BudgetLookupParams) (data : LookupTable p.toLookupParams)
    (rData : QRegister (p.m + p.w) n) (rAnc : QRegister (oldAnc p) n)
    (hdisj : rData.DisjointWires rAnc) :
    RealizesCleanSubroutineOnEncoding rData rAnc hdisj (unlookupValidInputs data)
      (tableXorPerm data.extend) (oldProg p data rData rAnc).compile := by
  by_cases h : SelectSwapImpl.ssCond p.m p.w p.a
  · unfold oldProg
    rw [dif_pos h]
    exact SelectSwapImpl.ssProg_realizes p.toLookupParams _ data rData rAnc _ h.1 hdisj _
  · unfold oldProg
    rw [dif_neg h]
    exact SelectSwapImpl.castReg_realizes p.toLookupParams data rData (SelectSwapImpl.ssAnc_neg h) rAnc hdisj _

theorem oldProg_realizes_cast (p : BudgetLookupParams) (data : LookupTable p.toLookupParams)
    (rData : QRegister (p.m + p.w) n) {N : ℕ} (hN : N = oldAnc p) (rAnc : QRegister N n)
    (hdisj : rData.DisjointWires rAnc) :
    RealizesCleanSubroutineOnEncoding rData rAnc hdisj (unlookupValidInputs data)
      (tableXorPerm data.extend)
      (oldProg p data rData (SelectSwapImpl.castReg hN rAnc)).compile := by
  subst hN
  exact oldProg_realizes p data rData rAnc hdisj

theorem oldAnc_le (p : BudgetLookupParams) (hp : p.Valid) : oldAnc p ≤ p.a := by
  by_cases h : SelectSwapImpl.ssCond p.m p.w p.a
  · show SelectSwapImpl.ssAnc p.m p.w p.a ≤ p.a
    rw [SelectSwapImpl.ssAnc_pos h]
    exact h.2.1
  · show SelectSwapImpl.ssAnc p.m p.w p.a ≤ p.a
    rw [SelectSwapImpl.ssAnc_neg h]
    exact hp.2

theorem oldProg_count (p : BudgetLookupParams) (data : LookupTable p.toLookupParams)
    (rData : QRegister (p.m + p.w) n) (rAnc : QRegister (oldAnc p) n) :
    (oldProg p data rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (oldProg p data rData rAnc).count PrimitiveGate.T ≤ oldTCost p.m p.w p.a := by
  by_cases h : SelectSwapImpl.ssCond p.m p.w p.a
  · refine ⟨?_, ?_⟩
    · unfold oldProg
      rw [dif_pos h]
      exact count_TOFF_compileList _ _
    · unfold oldProg oldTCost
      rw [dif_pos h, if_pos h]
      exact SelectSwapImpl.ssProg_count_T p.toLookupParams _ data rData rAnc _ h.1
  · refine ⟨?_, ?_⟩
    · unfold oldProg
      rw [dif_neg h]
      exact lookup_count_TOFF (Var.v 0) _ data rData _
    · unfold oldProg oldTCost
      rw [dif_neg h, if_neg h]
      exact lookup_count_T (Var.v 0) _ data rData _

end MbuImpl

namespace MblImpl

open Operator Matrix QProg Function TableLookupSteps TableLookupImpl SelectSwapImpl MbuImpl HermitianMat
open scoped Matrix ComplexOrder MatrixOrder

variable {n : ℕ}

/-- The first four parts of `ssSteps`: compute into `rD`, swap, copy, unswap. Afterwards `rD`
holds `wideTab s p.w f (xh)`. -/
def mblStage1 (p : LookupParams) (s : ℕ) (hs : s ≤ p.m) (f : ℕ → ℕ)
    (rData : QRegister (p.m + p.w) n) (rD : QRegister (2 ^ s * p.w) n)
    (rW : QRegister (p.m - s) n) (ci : Wire n) : List (Step n) :=
  lookupSteps (2 ^ s * p.w) rD (p.m - s) none (rData.slice (p.w + s) (p.m - s) (by omega)) rW
      (wideTab s p.w f) ++
    swapTree ci p.w (dataBlock s p.w rD) s (rData.slice p.w s (by omega)) ++
    copySteps p.w (dataBlock s p.w rD 0) (rData.slice 0 p.w (by omega)) ++
    (swapTree ci p.w (dataBlock s p.w rD) s (rData.slice p.w s (by omega))).reverse.map
      Step.inv

theorem runList_mblStage1 (p : LookupParams) (s : ℕ) (hs : s ≤ p.m) (f : ℕ → ℕ)
    (rData : QRegister (p.m + p.w) n) (rD : QRegister (2 ^ s * p.w) n)
    (rW : QRegister (p.m - s) n) (ci : Wire n)
    (hDl : rD.DisjointWires (rData.slice p.w s (by omega)))
    (hDh : rD.DisjointWires (rData.slice (p.w + s) (p.m - s) (by omega)))
    (hDW : rD.DisjointWires rW)
    (hDY : rD.DisjointWires (rData.slice 0 p.w (by omega)))
    (hlY : (rData.slice p.w s (by omega)).DisjointWires (rData.slice 0 p.w (by omega)))
    (hhW : (rData.slice (p.w + s) (p.m - s) (by omega)).DisjointWires rW)
    (hhY : (rData.slice (p.w + s) (p.m - s) (by omega)).DisjointWires
      (rData.slice 0 p.w (by omega)))
    (hWY : rW.DisjointWires (rData.slice 0 p.w (by omega)))
    (hiD : ci ∉ Set.range rD.wires) (hiXl : ci ∉ Set.range (rData.slice p.w s (by omega)).wires)
    (hiY : ci ∉ Set.range (rData.slice 0 p.w (by omega)).wires) (β : BitAssignment n)
    (hD : ∀ i, β (rD i) = 0) (hW : ∀ i, β (rW i) = 0) (hci : β ci = 0) :
    runList (mblStage1 p s hs f rData rD rW ci) β =
      some (writeReg (writeReg β rD (wideTab s p.w f
          (localIdx (rData.slice (p.w + s) (p.m - s) (by omega)) β)))
        (rData.slice 0 p.w (by omega)) (fun i ↦
        β (rData.slice 0 p.w (by omega) i) +
          tableBits p.w f ((localIdx (rData.slice p.w s (by omega)) β : ℕ) +
            2 ^ s * (localIdx (rData.slice (p.w + s) (p.m - s) (by omega)) β : ℕ)) i)) := by
  set rXl := rData.slice p.w s (by omega) with hrXl
  set rXh := rData.slice (p.w + s) (p.m - s) (by omega) with hrXh
  set rY := rData.slice 0 p.w (by omega) with hrY
  set B := dataBlock s p.w rD with hBdef
  set S := swapTree ci p.w B s rXl with hS
  have hnB : ∀ {v}, v ∉ Set.range rD.wires → ∀ l, v ∉ Set.range (B l).wires :=
    fun hv _ ↦ not_mem_slice hv _ _ _
  have hlook := fun β' ↦ runList_lookupSteps (2 ^ s * p.w) rD (p.m - s) none rXh rW
    (wideTab s p.w f) hhW
    (QRegister.disjoint_comm.mp hDh) (QRegister.disjoint_comm.mp hDW)
    (fun _ ↦ ctrlNe_none _) (fun _ ↦ ctrlNe_none _) (fun _ ↦ ctrlNe_none _) β'
  set x := (localIdx rXl β : ℕ) + 2 ^ s * (localIdx rXh β : ℕ) with hx
  set β1 := writeReg β rD (wideTab s p.w f (localIdx rXh β)) with hβ1
  have h1 : runList (lookupSteps (2 ^ s * p.w) rD (p.m - s) none rXh rW (wideTab s p.w f)) β =
      some β1 := by
    rw [hlook β hW]
    simp only [hD, ctrlVal, zero_add, one_mul]
    rfl
  have hb1 : ∀ v, v ∉ Set.range rD.wires → β1 v = β v := fun v hv ↦
    writeReg_apply_of_not_mem _ _ _ _ hv
  obtain ⟨β2, h2, hfr2_B, h2B⟩ := runList_swapTree ci p.w B s rXl
    (fun l l' hl hl' h ↦ dataBlock_disjoint s p.w rD hl hl' h)
    (fun j ↦ hnB (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDl) j))
    hiXl (hnB hiD) β1 (by rw [hb1 _ hiD, hci])
  have hfr2 : ∀ v, v ∉ Set.range rD.wires → β2 v = β1 v := fun v hv ↦ hfr2_B v (hnB hv)
  have hB0 : ∀ i, β2 (B 0 i) = tableBits p.w f x i := fun i ↦ by
    have hl := (localIdx rXl β).isLt
    rw [h2B, localIdx_writeReg_of_disjoint _ _ _ hDl, hβ1,
      writeReg_wideTab_dataBlock _ _ _ _ _ _ _ hl]
  have hrY2 : ∀ i, β2 (rY i) = β (rY i) := fun i ↦ by
    rw [hfr2 _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDY) i),
      hb1 _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDY) i)]
  set γ : BitAssignment p.w := fun i ↦ β (rY i) + tableBits p.w f x i with hγ
  have h3 : runList (copySteps p.w (B 0) rY) β2 = some (writeReg β2 rY γ) := by
    rw [runList_copySteps p.w (B 0) rY (hDY.compose_left _)]
    congr 2
    funext i
    rw [hB0, hrY2]
  have h4 : runList (S.reverse.map Step.inv) (writeReg β2 rY γ) = some (writeReg β1 rY γ) := by
    rw [runList_writeReg_of_avoids _ rY (fun st hst i ↦ by
        obtain ⟨st', hst', rfl⟩ := List.mem_map.mp hst
        exact Step.avoids_inv (swapTree_avoids ci p.w B s rXl _
          (fun h ↦ hiY ⟨i, h.symm⟩)
          (not_mem_of_disjoint (QRegister.disjoint_comm.mp hlY) i)
          (hnB (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDY) i))
          st' (List.mem_reverse.mp hst'))),
      runList_inv (swapTree_noUnxor ci p.w B s rXl) h2, Option.map_some]
  rw [mblStage1, runList_append, runList_append, runList_append, h1,
    Option.bind_some, ← hS, h2, Option.bind_some, h3, Option.bind_some, h4]

theorem mblStage1_ac (p : LookupParams) (s : ℕ) (hs : s ≤ p.m) (f : ℕ → ℕ)
    (rData : QRegister (p.m + p.w) n) (rD : QRegister (2 ^ s * p.w) n)
    (rW : QRegister (p.m - s) n) (ci : Wire n) :
    ac (mblStage1 p s hs f rData rD rW ci) + 2 * p.w ≤ (2 ^ (p.m - s) - 1) + 2 * (2 ^ s * p.w) := by
  have h1 : ac (lookupSteps (2 ^ s * p.w) rD (p.m - s) none
      (rData.slice (p.w + s) (p.m - s) (by omega)) rW (wideTab s p.w f)) ≤ 2 ^ (p.m - s) - 1 :=
    andCount_lookupSteps _ _ _ _ _ _ _
  have h2 := ac_swapTree ci p.w (dataBlock s p.w rD) s (rData.slice p.w s (by omega))
  have h3 := aci_swapTree ci p.w (dataBlock s p.w rD) s (rData.slice p.w s (by omega))
  have h4 := ac_copySteps p.w (dataBlock s p.w rD 0) (rData.slice 0 p.w (by omega))
  have h3' : ac ((swapTree ci p.w (dataBlock s p.w rD) s
      (rData.slice p.w s (by omega))).reverse.map Step.inv) + p.w = 2 ^ s * p.w := h3
  simp only [mblStage1, ac_append]
  omega

/-- The width-1 table of parities of the mask `r` against the junk register content. -/
def gTab (p : LookupParams) (s : ℕ) (f : ℕ → ℕ) (r : Fin (2 ^ s * p.w) → ZMod 2) (h : ℕ) : ℕ :=
  (∑ j, r j * wideTab s p.w f h j).val

theorem gTab_bit (p : LookupParams) (s : ℕ) (f : ℕ → ℕ) (r : Fin (2 ^ s * p.w) → ZMod 2)
    (h : ℕ) : tableBits 1 (gTab p s f r) h 0 = ∑ j, r j * wideTab s p.w f h j := by
  simp only [tableBits, gTab, Fin.val_zero, _root_.pow_zero, Nat.div_one]
  rw [ZMod.natCast_mod, ZMod.natCast_zmod_val]

theorem zeroL_finRange' {W : ℕ} (r : QRegister W n) (β : BitAssignment n) :
    zeroL (fun i ↦ r i) (List.finRange W) β = writeReg β r (fun _ ↦ 0) := by
  funext v
  rw [zeroL_apply]
  by_cases hv : v ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hv
    rw [if_pos ⟨i, List.mem_finRange _, rfl⟩]
    exact (writeReg_apply_reg β r (fun _ ↦ 0) i).symm
  · rw [writeReg_apply_of_not_mem _ _ _ _ hv, if_neg]
    rintro ⟨i, -, rfl⟩
    exact hv ⟨i, rfl⟩

/-- Stage 2 leaf: width-1 phase lookup over the high address bits. -/
def mblLeaf (p : LookupParams) (s s2 : ℕ) (hs : s ≤ p.m) (hs2 : s2 ≤ p.m - s)
    (data : LookupTable p) (rData : QRegister (p.m + p.w) n) {N : ℕ} (rAnc : QRegister N n)
    (hN : 2 ^ s * p.w + (p.m - s) + 1 + (2 ^ s2 * 1 + (p.m - s - s2) + 1) ≤ N)
    (r : Fin (2 ^ s * p.w) → ZMod 2) : DynamicCircuit Var n :=
  leafCirc (p.m - s) s2 (gTab p s (fTab data) r)
    ((rData.slice (p.w + s) (p.m - s) (by omega)).slice 0 s2 (by omega))
    ((rData.slice (p.w + s) (p.m - s) (by omega)).slice s2 (p.m - s - s2) (by omega))
    (rAnc.slice (2 ^ s * p.w + (p.m - s) + 1 + 2 ^ s2 * 1) (p.m - s - s2) (by omega))
    (rAnc.slice (2 ^ s * p.w + (p.m - s) + 1) (2 ^ s2 * 1) (by omega))
    (rAnc ⟨2 ^ s * p.w + (p.m - s) + 1 + 2 ^ s2 * 1 + (p.m - s - s2), by omega⟩)

/-- Lookup with measurement-based cleanup of the junk register. -/
def mblProg (p : LookupParams) (s s2 : ℕ) (hs : s ≤ p.m) (hs2 : s2 ≤ p.m - s)
    (data : LookupTable p) (rData : QRegister (p.m + p.w) n) {N : ℕ} (rAnc : QRegister N n)
    (hN : 2 ^ s * p.w + (p.m - s) + 1 + (2 ^ s2 * 1 + (p.m - s - s2) + 1) ≤ N) :
    DynamicCircuit Var n :=
  .seq (compileList (Var.v 0) (mblStage1 p s hs (fTab data) rData
      (rAnc.slice 0 (2 ^ s * p.w) (by omega)) (rAnc.slice (2 ^ s * p.w) (p.m - s) (by omega))
      (rAnc ⟨2 ^ s * p.w + (p.m - s), by omega⟩)))
    (mbuTree (Var.v 0) (fun i ↦ rAnc.slice 0 (2 ^ s * p.w) (by omega) i)
      (mblLeaf p s s2 hs hs2 data rData rAnc hN) (List.finRange (2 ^ s * p.w)) (fun _ ↦ 0))

theorem mblProg_count_T (p : LookupParams) (s s2 : ℕ) (hs : s ≤ p.m) (hs2 : s2 ≤ p.m - s)
    (data : LookupTable p) (rData : QRegister (p.m + p.w) n) {N : ℕ} (rAnc : QRegister N n)
    (hN : 2 ^ s * p.w + (p.m - s) + 1 + (2 ^ s2 * 1 + (p.m - s - s2) + 1) ≤ N) :
    (mblProg p s s2 hs hs2 data rData rAnc hN).count PrimitiveGate.T ≤
      4 * (2 ^ (p.m - s) - 1) + 8 * (2 ^ s - 1) * p.w + ssT (p.m - s) 1 s2 := by
  have h1 := count_T_compileList (Var.v 0) (mblStage1 p s hs (fTab data) rData
      (rAnc.slice 0 (2 ^ s * p.w) (by omega)) (rAnc.slice (2 ^ s * p.w) (p.m - s) (by omega))
      (rAnc ⟨2 ^ s * p.w + (p.m - s), by omega⟩))
  have h2 := mblStage1_ac p s hs (fTab data) rData
      (rAnc.slice 0 (2 ^ s * p.w) (by omega)) (rAnc.slice (2 ^ s * p.w) (p.m - s) (by omega))
      (rAnc ⟨2 ^ s * p.w + (p.m - s), by omega⟩)
  have h3 : (mbuTree (Var.v 0) (fun i ↦ rAnc.slice 0 (2 ^ s * p.w) (by omega) i)
      (mblLeaf p s s2 hs hs2 data rData rAnc hN) (List.finRange (2 ^ s * p.w))
      (fun _ ↦ 0)).count PrimitiveGate.T ≤ ssT (p.m - s) 1 s2 :=
    mbuTree_count _ _ _ _ _ (fun q ↦ by simp) (fun q ↦ by simp)
      (fun r ↦ leafCirc_count_T _ _ hs2 _ _ _ _ _ _) _ _
  have e : ((mblStage1 p s hs (fTab data) rData
      (rAnc.slice 0 (2 ^ s * p.w) (by omega)) (rAnc.slice (2 ^ s * p.w) (p.m - s) (by omega))
      (rAnc ⟨2 ^ s * p.w + (p.m - s), by omega⟩)).map Step.andCount).sum = ac (mblStage1 p s hs
      (fTab data) rData
      (rAnc.slice 0 (2 ^ s * p.w) (by omega)) (rAnc.slice (2 ^ s * p.w) (p.m - s) (by omega))
      (rAnc ⟨2 ^ s * p.w + (p.m - s), by omega⟩)) := rfl
  rw [e] at h1
  have h4 : 8 * (2 ^ s - 1) * p.w + 8 * p.w = 8 * (2 ^ s * p.w) := by
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ s = k + 1 := ⟨2 ^ s - 1, by have := @Nat.one_le_two_pow s; omega⟩
    rw [hk, Nat.add_sub_cancel]
    ring
  unfold mblProg
  simp only [DynamicCircuit.count]
  omega

theorem mblProg_count_TOFF (p : LookupParams) (s s2 : ℕ) (hs : s ≤ p.m) (hs2 : s2 ≤ p.m - s)
    (data : LookupTable p) (rData : QRegister (p.m + p.w) n) {N : ℕ} (rAnc : QRegister N n)
    (hN : 2 ^ s * p.w + (p.m - s) + 1 + (2 ^ s2 * 1 + (p.m - s - s2) + 1) ≤ N) :
    (mblProg p s s2 hs hs2 data rData rAnc hN).count PrimitiveGate.TOFF = 0 := by
  have h3 := mbuTree_count (Var.v 0) (fun i ↦ rAnc.slice 0 (2 ^ s * p.w) (by omega) i)
      (mblLeaf p s s2 hs hs2 data rData rAnc hN) PrimitiveGate.TOFF 0
      (fun q ↦ by simp) (fun q ↦ by simp)
      (fun r ↦ (leafCirc_count_TOFF _ _ _ _ _ _ _ _).le) (List.finRange (2 ^ s * p.w))
      (fun _ ↦ 0)
  have h1 := count_TOFF_compileList (Var.v 0) (mblStage1 p s hs (fTab data) rData
      (rAnc.slice 0 (2 ^ s * p.w) (by omega)) (rAnc.slice (2 ^ s * p.w) (p.m - s) (by omega))
      (rAnc ⟨2 ^ s * p.w + (p.m - s), by omega⟩))
  unfold mblProg
  simp only [DynamicCircuit.count]
  omega

theorem mblProg_realizes (p : LookupParams) (s s2 : ℕ) (hs : s ≤ p.m) (hs2 : s2 ≤ p.m - s)
    (data : LookupTable p) (rData : QRegister (p.m + p.w) n) {N : ℕ} (rAnc : QRegister N n)
    (hN : 2 ^ s * p.w + (p.m - s) + 1 + (2 ^ s2 * 1 + (p.m - s - s2) + 1) ≤ N)
    (hd : rData.DisjointWires rAnc) (V : Set (Fin (2 ^ (p.m + p.w)))) :
    RealizesCleanSubroutineOnEncoding rData rAnc hd V (tableXorPerm data.extend)
      (mblProg p s s2 hs hs2 data rData rAnc hN).compile := by
  haveI : NeZero (2 ^ n) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hDA : ∀ {a b : ℕ} (r : QRegister a (p.m + p.w)) (r' : QRegister b N),
      (rAnc.compose r').DisjointWires (rData.compose r) := fun _ _ ↦
    QRegister.disjoint_comm.mp ((hd.compose_left _).compose_right _)
  have hXA : ∀ {a b : ℕ} (r : QRegister a (p.m - s)) (r' : QRegister b N),
      (rAnc.compose r').DisjointWires ((rData.slice (p.w + s) (p.m - s) (by omega)).compose r) :=
    fun r r' ↦ QRegister.disjoint_comm.mp
      (((hd.compose_left (QRegister.block (p.w + s) (p.m - s) (by omega))).compose_left r).compose_right r')
  have hTA : (targetReg p rData).DisjointWires rAnc := hd.compose_left _
  have hYX : (targetReg p rData).DisjointWires (addrReg p rData) :=
    rData.slice_disjoint_of_le 0 p.w p.w p.m _ _ (by omega)
  have hx : ∀ γ : BitAssignment n, (localIdx (addrReg p rData) γ : ℕ) =
      (localIdx (rData.slice p.w s (by omega)) γ : ℕ) +
        2 ^ s * (localIdx (rData.slice (p.w + s) (p.m - s) (by omega)) γ : ℕ) := fun γ ↦ by
    rw [localIdx_val_split (addrReg p rData) s (p.m - s) (by omega)]
    simp only [localIdx_slice_slice, add_zero]
  have hxh : ∀ γ : BitAssignment n,
      (localIdx ((rData.slice (p.w + s) (p.m - s) (by omega)).slice 0 s2 (by omega)) γ : ℕ) +
        2 ^ s2 * (localIdx ((rData.slice (p.w + s) (p.m - s) (by omega)).slice s2
          (p.m - s - s2) (by omega)) γ : ℕ) =
        (localIdx (rData.slice (p.w + s) (p.m - s) (by omega)) γ : ℕ) := fun γ ↦
    (localIdx_val_split (rData.slice (p.w + s) (p.m - s) (by omega)) s2 (p.m - s - s2)
      (by omega) γ).symm
  obtain ⟨R1, hK1, hR1, -⟩ := exists_lowerKraus_compileList (Var.v 0) (mblStage1 p s hs (fTab data)
    rData (rAnc.slice 0 (2 ^ s * p.w) (by omega)) (rAnc.slice (2 ^ s * p.w) (p.m - s) (by omega))
    (rAnc ⟨2 ^ s * p.w + (p.m - s), by omega⟩))
  obtain ⟨R2, hK2, hR2⟩ := mbuTree_kraus (Var.v 0) (fun i ↦ rAnc.slice 0 (2 ^ s * p.w) (by omega) i)
    (mblLeaf p s s2 hs hs2 data rData rAnc hN)
    (fun i γ ↦ wideTab s p.w (fTab data) (localIdx (rData.slice (p.w + s) (p.m - s) (by omega)) γ) i)
    (fun γ ↦ ∀ k : Fin N, 2 ^ s * p.w + (p.m - s) + 1 ≤ k.val → γ (rAnc k) = 0)
    (fun i j h ↦ (rAnc.slice 0 (2 ^ s * p.w) (by omega)).wires.injective h)
    (fun γ i a h k hk ↦ by
      rw [update_of_ne]
      · exact h k hk
      · intro e
        have := rAnc.wires.injective e
        have h2 : 0 + (i : ℕ) = (k : ℕ) := (congrArg Fin.val this).symm
        have h3 := i.isLt
        omega)
    (fun γ i j a ↦ by
      simp only [localIdx_update_of_not_mem _ γ (not_mem_of_disjoint (hDA _ _) i) a])
    (fun r ↦ by
      obtain ⟨L, hL, hLk⟩ := leafCirc_kraus (p.m - s) s2 (gTab p s (fTab data) r)
        ((rData.slice (p.w + s) (p.m - s) (by omega)).slice 0 s2 (by omega))
        ((rData.slice (p.w + s) (p.m - s) (by omega)).slice s2 (p.m - s - s2) (by omega))
        (rAnc.slice (2 ^ s * p.w + (p.m - s) + 1 + 2 ^ s2 * 1) (p.m - s - s2) (by omega))
        (rAnc.slice (2 ^ s * p.w + (p.m - s) + 1) (2 ^ s2 * 1) (by omega))
        (rAnc ⟨2 ^ s * p.w + (p.m - s) + 1 + 2 ^ s2 * 1 + (p.m - s - s2), by omega⟩)
        (hXA _ _) (hXA _ _)
        (QRegister.slice_disjoint_of_le rAnc _ _ _ _ (by omega) (by omega) (by omega))
        (QRegister.disjoint_comm.mp (hXA _ _))
        (apply_not_mem_slice rAnc _ (2 ^ s * p.w + (p.m - s) + 1) _ (by omega) (Or.inr (by simp)))
        (fun ⟨i, h⟩ ↦ ((hd.compose_left (QRegister.block (p.w + s) (p.m - s) (by omega))).compose_left
          (QRegister.block 0 s2 (by omega))).ne i _ h)
      refine ⟨L, hL, fun γ hγ ↦ ?_⟩
      have hD0 : ∀ i : Fin (2 ^ s2 * 1), γ (rAnc.slice (2 ^ s * p.w + (p.m - s) + 1)
          (2 ^ s2 * 1) (by omega) i) = 0 := fun i ↦ by
        have := i.isLt
        exact hγ ⟨2 ^ s * p.w + (p.m - s) + 1 + i, by omega⟩ (Nat.le_add_right _ _)
      have hW0 : ∀ i : Fin (p.m - s - s2), γ (rAnc.slice (2 ^ s * p.w + (p.m - s) + 1 +
          2 ^ s2 * 1) (p.m - s - s2) (by omega) i) = 0 := fun i ↦ by
        have := i.isLt
        exact hγ ⟨2 ^ s * p.w + (p.m - s) + 1 + 2 ^ s2 * 1 + i, by omega⟩
          (by change _ ≤ 2 ^ s * p.w + (p.m - s) + 1 + 2 ^ s2 * 1 + (i : ℕ); omega)
      have hc0 : γ (rAnc ⟨2 ^ s * p.w + (p.m - s) + 1 + 2 ^ s2 * 1 + (p.m - s - s2),
          by omega⟩) = 0 :=
        hγ _ (by change _ ≤ 2 ^ s * p.w + (p.m - s) + 1 + 2 ^ s2 * 1 + (p.m - s - s2); omega)
      rw [hLk γ hD0 hW0 hc0, hxh γ, gTab_bit])
    (List.finRange (2 ^ s * p.w)) (List.nodup_finRange _) (fun _ ↦ 0)
  refine realizesOnEncoding_of_lowerKraus rData rAnc hd V _ (hK1.qSeq hK2) fun β h0 _ ↦ ?_
  have hclean := eq_zero_of_localIdx_eq_zero rAnc β h0
  have hD0 : ∀ i, β (rAnc.slice 0 (2 ^ s * p.w) (by omega) i) = 0 := fun _ ↦ hclean _
  have hW0 : ∀ i, β (rAnc.slice (2 ^ s * p.w) (p.m - s) (by omega) i) = 0 := fun _ ↦ hclean _
  have hst := runList_mblStage1 p s hs (fTab data) rData (rAnc.slice 0 (2 ^ s * p.w) (by omega))
    (rAnc.slice (2 ^ s * p.w) (p.m - s) (by omega)) (rAnc ⟨2 ^ s * p.w + (p.m - s), by omega⟩)
    (hDA _ _) (hDA _ _)
    (QRegister.slice_disjoint_of_le rAnc _ _ _ _ (by omega) (by omega) (by omega)) (hDA _ _)
    (QRegister.disjoint_comm.mp
      (QRegister.slice_disjoint_of_le rData _ _ _ _ (by omega) (by omega) (by omega)))
    (QRegister.disjoint_comm.mp (hDA _ _))
    (QRegister.disjoint_comm.mp
      (QRegister.slice_disjoint_of_le rData _ _ _ _ (by omega) (by omega) (by omega)))
    (hDA _ _)
    (apply_not_mem_slice rAnc _ 0 _ (by omega) (Or.inr (by simp)))
    (fun ⟨_, h⟩ ↦ hd.ne _ _ h)
    (fun ⟨_, h⟩ ↦ hd.ne _ _ h)
    β hD0 hW0 (hclean _)
  set rD := rAnc.slice 0 (2 ^ s * p.w) (by omega) with hrD
  set rXh := rData.slice (p.w + s) (p.m - s) (by omega) with hrXh
  set rY := rData.slice 0 p.w (by omega) with hrY
  have hDY : rD.DisjointWires rY := hDA _ _
  have hYA : rY.DisjointWires rAnc := hd.compose_left _
  set β1 := writeReg (writeReg β rD (wideTab s p.w (fTab data) (localIdx rXh β))) rY
    (fun i ↦ β (rY i) + tableBits p.w (fTab data)
      ((localIdx (rData.slice p.w s (by omega)) β : ℕ) + 2 ^ s * (localIdx rXh β : ℕ)) i)
    with hβ1
  have hG : ∀ k : Fin N, 2 ^ s * p.w + (p.m - s) + 1 ≤ k.val → β1 (rAnc k) = 0 := by
    intro k hk
    rw [hβ1, writeReg_apply_of_not_mem _ _ _ _ (fun ⟨i, h⟩ ↦ hYA.ne i k h),
      writeReg_apply_of_not_mem _ _ _ _ (apply_not_mem_slice rAnc k 0 _ (by omega)
        (Or.inr (by omega)))]
    exact hclean k
  have hcond : ∀ i ∈ List.finRange (2 ^ s * p.w),
      β1 (rD i) = wideTab s p.w (fTab data) (localIdx rXh β1) i := by
    intro i _
    rw [hβ1, writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hDY i), writeReg_apply_reg,
      localIdx_writeReg_of_disjoint _ _ _
        (rData.slice_disjoint_of_le 0 p.w (p.w + s) (p.m - s) (by omega) (by omega) (by omega)),
      localIdx_writeReg_of_disjoint _ _ _ (hDA _ _)]
  rw [← Matrix.mulVec_mulVec, hR1 _ _ hst, hR2 _ hG, if_pos hcond]
  simp only [zero_mul, Finset.sum_const_zero, bitSign, if_true, one_smul]
  rw [zeroL_finRange', hβ1, writeReg_comm _ rY rD (QRegister.disjoint_comm.mp hDY),
    writeReg_writeReg,
    show (fun _ : Fin (2 ^ s * p.w) ↦ (0 : ZMod 2)) = fun i ↦ β (rD i) from
      funext fun i ↦ (hD0 i).symm, writeReg_self, ← target_xor_eq data rData β]
  have hx : (localIdx (addrReg p rData) β : ℕ) =
      (localIdx (rData.slice p.w s (by omega)) β : ℕ) + 2 ^ s * (localIdx rXh β : ℕ) := by
    rw [localIdx_val_split (addrReg p rData) s (p.m - s) (by omega)]
    simp only [localIdx_slice_slice, add_zero]
    rfl
  congr 2
  funext i
  rw [← hx]
  exact congrArg (β (rY i) + ·) (congrFun (hbits data _ (localIdx (addrReg p rData) β).isLt) i)

/-- `T` count of the measurement-cleanup lookup with swap depths `s` and `s2`. -/
def mblT (m w s s2 : ℕ) : ℕ := 4 * (2 ^ (m - s) - 1) + 8 * (2 ^ s - 1) * w + ssT (m - s) 1 s2

/-- Second swap depth: best select-swap depth for the width-1 phase lookup in the remaining
budget. -/
def mblS2 (m w a s : ℕ) : ℕ := ssBest (m - s) 1 (a - ssA m w s)

/-- Clean ancillas of the measurement-cleanup lookup. -/
def mblA (m w s s2 : ℕ) : ℕ := ssA m w s + ssA (m - s) 1 s2

/-- Swap depth in `0..m` minimizing `mblT` among those with `mblA ≤ a` (ties to the smaller `s`). -/
def mblBest (m w a : ℕ) : ℕ :=
  (List.range (m + 1)).foldl
    (fun b s ↦ if mblA m w s (mblS2 m w a s) ≤ a ∧
        (a < mblA m w b (mblS2 m w a b) ∨ mblT m w s (mblS2 m w a s) < mblT m w b (mblS2 m w a b))
      then s else b) 0

/-- Use the measurement-cleanup lookup. -/
def mblCond (m w a : ℕ) : Prop :=
  mblBest m w a ≤ m ∧ mblS2 m w a (mblBest m w a) ≤ m - mblBest m w a ∧
    mblA m w (mblBest m w a) (mblS2 m w a (mblBest m w a)) ≤ a ∧
    mblT m w (mblBest m w a) (mblS2 m w a (mblBest m w a)) < oldTCost m w a

instance (m w a : ℕ) : Decidable (mblCond m w a) := by unfold mblCond; infer_instance

theorem oldProgL_realizes (p : BudgetLookupParams) (data : LookupTable p.toLookupParams)
    (rData : QRegister (p.m + p.w) n) (rAnc : QRegister (oldAnc p) n)
    (hdisj : rData.DisjointWires rAnc) (V : Set (Fin (2 ^ (p.m + p.w)))) :
    RealizesCleanSubroutineOnEncoding rData rAnc hdisj V
      (tableXorPerm data.extend) (oldProg p data rData rAnc).compile := by
  by_cases h : SelectSwapImpl.ssCond p.m p.w p.a
  · unfold oldProg
    rw [dif_pos h]
    exact SelectSwapImpl.ssProg_realizes p.toLookupParams _ data rData rAnc _ h.1 hdisj _
  · unfold oldProg
    rw [dif_neg h]
    exact SelectSwapImpl.castReg_realizes p.toLookupParams data rData (SelectSwapImpl.ssAnc_neg h) rAnc hdisj _

theorem oldProgL_realizes_cast (p : BudgetLookupParams) (data : LookupTable p.toLookupParams)
    (rData : QRegister (p.m + p.w) n) {N : ℕ} (hN : N = oldAnc p) (rAnc : QRegister N n)
    (hdisj : rData.DisjointWires rAnc) (V : Set (Fin (2 ^ (p.m + p.w)))) :
    RealizesCleanSubroutineOnEncoding rData rAnc hdisj V
      (tableXorPerm data.extend)
      (oldProg p data rData (SelectSwapImpl.castReg hN rAnc)).compile := by
  subst hN
  exact oldProgL_realizes p data rData rAnc hdisj V

end MblImpl

namespace Mbl2Impl

open Operator Matrix QProg Function TableLookupSteps TableLookupImpl SelectSwapImpl MbuImpl HermitianMat
open scoped Matrix ComplexOrder MatrixOrder

variable {n : ℕ}

/-- `runList_levelSwap` together with the content of the upper blocks `B (l + off)`. -/
theorem runList_levelSwap_full (c w_clean : Wire n) (w : ℕ) (B : ℕ → QRegister w n)
    (off k : ℕ) (hk : k ≤ off)
    (hD : ∀ l l', l < 2 * off → l' < 2 * off → l ≠ l' → (B l).DisjointWires (B l'))
    (hc : ∀ l, c ∉ Set.range (B l).wires) (hwc : c ≠ w_clean)
    (hwB : ∀ l, w_clean ∉ Set.range (B l).wires)
    (β : BitAssignment n) (hw0 : β w_clean = 0) :
    ∃ β', runList (levelSwap c w_clean w B off k) β = some β' ∧
      (∀ v, (∀ l < k, v ∉ Set.range (B l).wires ∧ v ∉ Set.range (B (l + off)).wires) →
        β' v = β v) ∧
      (∀ l < k, ∀ i, β' (B l i) = β (B (l + off * (β c).val) i)) ∧
      ∀ l < k, ∀ i, β' (B (l + off) i) = β (B (l + off * (1 - (β c).val)) i) := by
  induction k with
  | zero =>
    exact ⟨β, rfl, fun _ _ ↦ rfl, fun l hl ↦ absurd hl (Nat.not_lt_zero l),
      fun l hl ↦ absurd hl (Nat.not_lt_zero l)⟩
  | succ k ih =>
    obtain ⟨β1, h1, hfr1, h1B, h1B'⟩ := ih (by omega)
    obtain ⟨β2, h2, hfr2, h2A, h2B⟩ := runList_cswapSteps c w_clean w (B k) (B (k + off))
      (hD _ _ (by omega) (by omega) (by omega)) (hc _) (hc _) hwc (hwB _) (hwB _) β1
      (by rw [hfr1 w_clean fun l _ ↦ ⟨hwB l, hwB _⟩, hw0])
    have hc1 : β1 c = β c := hfr1 c fun l _ ↦ ⟨hc l, hc _⟩
    have dis : ∀ a b, a < 2 * off → b < 2 * off → a ≠ b → ∀ i,
        B a i ∉ Set.range (B b).wires := fun a b ha hb hab i ↦
      not_mem_of_disjoint (hD a b ha hb hab) i
    have e1 : ∀ i, β1 (B k i) = β (B k i) := fun i ↦
      hfr1 _ fun l' hl' ↦ ⟨dis k l' (by omega) (by omega) (by omega) i,
        dis k (l' + off) (by omega) (by omega) (by omega) i⟩
    have e2 : ∀ i, β1 (B (k + off) i) = β (B (k + off) i) := fun i ↦
      hfr1 _ fun l' hl' ↦ ⟨dis (k + off) l' (by omega) (by omega) (by omega) i,
        dis (k + off) (l' + off) (by omega) (by omega) (by omega) i⟩
    refine ⟨β2, by rw [levelSwap, runList_append, h1, Option.bind_some, h2],
      fun v hv ↦ by
        rw [hfr2 v (hv k (by omega)).1 (hv k (by omega)).2,
          hfr1 v fun l hl ↦ hv l (by omega)],
      fun l hl i ↦ ?_, fun l hl i ↦ ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | hl
      · rw [hfr2 _ (dis l k (by omega) (by omega) (by omega) i)
          (dis l (k + off) (by omega) (by omega) (by omega) i), h1B l hl i]
      · subst hl
        rw [h2A, hc1, e1, e2]
        rcases bit_cases (β c) with h | h <;> rw [h]
        · simp
        · rw [one_mul, ← add_assoc, CharTwo.add_self_eq_zero, zero_add,
            show ZMod.val (1 : ZMod 2) = 1 from rfl, mul_one]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | hl
      · rw [hfr2 _ (dis (l + off) k (by omega) (by omega) (by omega) i)
          (dis (l + off) (k + off) (by omega) (by omega) (by omega) i), h1B' l hl i]
      · subst hl
        rw [h2B, hc1, e1, e2]
        rcases bit_cases (β c) with h | h <;> rw [h]
        · simp
        · rw [one_mul, add_comm (β (B l i)) (β (B (l + off) i)), ← add_assoc,
            CharTwo.add_self_eq_zero, zero_add,
            show ZMod.val (1 : ZMod 2) = 1 from rfl, Nat.sub_self, mul_zero, add_zero]

/-- The block that ends up in position `j` after `swapTree` on the address `xl`. -/
def swapSrc : ℕ → ℕ → ℕ → ℕ
  | 0, _, j => j
  | s + 1, xl, j =>
    if j < 2 ^ s then swapSrc s (xl % 2 ^ s) j + 2 ^ s * (xl / 2 ^ s % 2)
    else j - 2 ^ s * (xl / 2 ^ s % 2)

theorem swapSrc_lt (s : ℕ) : ∀ xl j, j < 2 ^ s → swapSrc s xl j < 2 ^ s := by
  induction s with
  | zero => intro xl j hj; simpa [swapSrc] using hj
  | succ s ih =>
    intro xl j hj
    have hb := Nat.mod_lt (xl / 2 ^ s) (show 0 < 2 by norm_num)
    have hm : 2 ^ s * (xl / 2 ^ s % 2) ≤ 2 ^ s * 1 := Nat.mul_le_mul_left _ (by omega)
    rw [pow_succ] at hj ⊢
    simp only [swapSrc]
    split_ifs with h
    · have := ih (xl % 2 ^ s) j h
      omega
    · omega

theorem swapSrc_zero (s : ℕ) : ∀ xl, xl < 2 ^ s → swapSrc s xl 0 = xl := by
  induction s with
  | zero => intro xl h; simp at h; simp [swapSrc, h]
  | succ s ih =>
    intro xl h
    have h0 : 0 < 2 ^ s := by positivity
    rw [pow_succ] at h
    simp only [swapSrc, if_pos h0]
    rw [ih (xl % 2 ^ s) (Nat.mod_lt _ h0),
      Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul h)]
    exact Nat.mod_add_div xl (2 ^ s)

theorem swapSrc_succ_split (s L T j : ℕ) (hL : L < 2 ^ s) (hT : T < 2) :
    swapSrc (s + 1) (L + 2 ^ s * T) j =
      if j < 2 ^ s then swapSrc s L j + 2 ^ s * T else j - 2 ^ s * T := by
  have e1 : (L + 2 ^ s * T) % 2 ^ s = L := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hL]
  have e2 : (L + 2 ^ s * T) / 2 ^ s % 2 = T := by
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hL, zero_add,
      Nat.mod_eq_of_lt hT]
  simp only [swapSrc, e1, e2]

theorem runList_swapTree_full (w_clean : Wire n) (w : ℕ) (B : ℕ → QRegister w n) (s : ℕ)
    (rc : QRegister s n)
    (hD : ∀ l l', l < 2 ^ s → l' < 2 ^ s → l ≠ l' → (B l).DisjointWires (B l'))
    (hc : ∀ j l, rc j ∉ Set.range (B l).wires)
    (hwrc : w_clean ∉ Set.range rc.wires) (hwB : ∀ l, w_clean ∉ Set.range (B l).wires)
    (β : BitAssignment n) (hw0 : β w_clean = 0) :
    ∃ β', runList (swapTree w_clean w B s rc) β = some β' ∧
      (∀ v, (∀ l < 2 ^ s, v ∉ Set.range (B l).wires) → β' v = β v) ∧
      ∀ j < 2 ^ s, ∀ i, β' (B j i) = β (B (swapSrc s (localIdx rc β) j) i) := by
  induction s generalizing β with
  | zero =>
    exact ⟨β, rfl, fun _ _ ↦ rfl, fun j hj i ↦ by simp [swapSrc]⟩
  | succ s ih =>
    obtain ⟨β1, h1, hfr1, h1B, h1B'⟩ := runList_levelSwap_full (rc (Fin.last s)) w_clean w B
      (2 ^ s) (2 ^ s) le_rfl
      (fun l l' hl hl' ↦ hD l l' (by rw [pow_succ]; omega) (by rw [pow_succ]; omega))
      (hc _) (fun h ↦ hwrc ⟨Fin.last s, h⟩) hwB β hw0
    have hc' : ∀ j l, (rc.slice 0 s (by omega)) j ∉ Set.range (B l).wires := fun j l ↦ by
      rw [QRegister.slice_apply]
      exact hc _ l
    obtain ⟨β2, h2, hfr2, h2B⟩ := ih (rc.slice 0 s (by omega))
      (fun l l' hl hl' ↦ hD l l' (by rw [pow_succ]; omega) (by rw [pow_succ]; omega)) hc'
      (not_mem_slice hwrc 0 s (by omega)) β1
      (by rw [hfr1 w_clean fun l _ ↦ ⟨hwB l, hwB _⟩, hw0])
    have hrc : localIdx (rc.slice 0 s (by omega)) β1 = localIdx (rc.slice 0 s (by omega)) β := by
      simp only [localIdx]
      congr 1
      funext j
      exact hfr1 _ fun l _ ↦ ⟨hc' j l, hc' j _⟩
    have hlast : (localIdx (rc.slice s 1 (by omega)) β : ℕ) = (β (rc (Fin.last s))).val := by
      rw [localIdx_val, Fin.sum_univ_one, QRegister.slice_apply]
      simp only [Fin.val_zero, _root_.pow_zero, mul_one, add_zero]
      rfl
    have hL : (localIdx (rc.slice 0 s (by omega)) β : ℕ) < 2 ^ s := (localIdx _ _).isLt
    have hT : (β (rc (Fin.last s))).val < 2 := ZMod.val_lt _
    have hsplit : (localIdx rc β : ℕ) = (localIdx (rc.slice 0 s (by omega)) β : ℕ) +
        2 ^ s * (β (rc (Fin.last s))).val := by
      rw [localIdx_val_split rc s 1 rfl β, hlast]
    refine ⟨β2, by rw [swapTree, runList_append, h1, Option.bind_some, h2],
      fun v hv ↦ by
        rw [hfr2 v fun l hl ↦ hv l (by rw [pow_succ]; omega),
          hfr1 v fun l hl ↦ ⟨hv l (by rw [pow_succ]; omega),
            hv (l + 2 ^ s) (by rw [pow_succ]; omega)⟩],
      fun j hj i ↦ ?_⟩
    rw [hsplit, swapSrc_succ_split _ _ _ _ hL hT]
    split_ifs with hjs
    · rw [h2B j hjs i, hrc, h1B _ (swapSrc_lt s _ j hjs) i]
    · obtain ⟨l, rfl⟩ : ∃ l, j = l + 2 ^ s := ⟨j - 2 ^ s, by omega⟩
      have hl : l < 2 ^ s := by rw [pow_succ] at hj; omega
      rw [hfr2 _ (fun l' hl' ↦ not_mem_of_disjoint
        (hD (l + 2 ^ s) l' (by rw [pow_succ]; omega) (by rw [pow_succ]; omega) (by omega)) i),
        h1B' l hl i]
      have key : ∀ T l : ℕ, T < 2 → l + 2 ^ s * (1 - T) = l + 2 ^ s - 2 ^ s * T := by
        intro T l hT
        rcases (by omega : T = 0 ∨ T = 1) with rfl | rfl <;> simp
      rw [key _ _ hT]

/-- The first three parts of `ssSteps`: compute into `rD`, swap, copy (no unswap). -/
def mbl2Stage1 (p : LookupParams) (s : ℕ) (hs : s ≤ p.m) (f : ℕ → ℕ)
    (rData : QRegister (p.m + p.w) n) (rD : QRegister (2 ^ s * p.w) n)
    (rW : QRegister (p.m - s) n) (ci : Wire n) : List (Step n) :=
  lookupSteps (2 ^ s * p.w) rD (p.m - s) none (rData.slice (p.w + s) (p.m - s) (by omega)) rW
      (wideTab s p.w f) ++
    swapTree ci p.w (dataBlock s p.w rD) s (rData.slice p.w s (by omega)) ++
    copySteps p.w (dataBlock s p.w rD 0) (rData.slice 0 p.w (by omega))

/-- Content of the junk register after the swap tree: block `j` holds the table entry at
`swapSrc s xl j + 2^s xh`. -/
def swTab (s w : ℕ) (f : ℕ → ℕ) (xl xh : ℕ) : BitAssignment (2 ^ s * w) :=
  fun q ↦ tableBits w f (swapSrc s xl ((q : ℕ) / w) + 2 ^ s * xh)
    ⟨(q : ℕ) % w, Nat.mod_lt _ (Nat.pos_of_ne_zero (by
      rintro rfl
      exact absurd q.isLt (by simp)))⟩

theorem rD_eq_block (s w : ℕ) (rD : QRegister (2 ^ s * w) n) (q : Fin (2 ^ s * w))
    (hw : 0 < w) :
    rD q = dataBlock s w rD ((q : ℕ) / w) ⟨(q : ℕ) % w, Nat.mod_lt _ hw⟩ := by
  have hj : (q : ℕ) / w < 2 ^ s := Nat.div_lt_of_lt_mul (lt_of_lt_of_eq q.isLt (mul_comm _ _))
  rw [dataBlock, QRegister.slice_apply]
  congr 1
  apply Fin.ext
  simp only [Nat.mod_eq_of_lt hj]
  exact (Nat.div_add_mod' _ _).symm

theorem runList_mbl2Stage1 (p : LookupParams) (s : ℕ) (hs : s ≤ p.m) (f : ℕ → ℕ)
    (rData : QRegister (p.m + p.w) n) (rD : QRegister (2 ^ s * p.w) n)
    (rW : QRegister (p.m - s) n) (ci : Wire n)
    (hDl : rD.DisjointWires (rData.slice p.w s (by omega)))
    (hDh : rD.DisjointWires (rData.slice (p.w + s) (p.m - s) (by omega)))
    (hDW : rD.DisjointWires rW)
    (hDY : rD.DisjointWires (rData.slice 0 p.w (by omega)))
    (hlY : (rData.slice p.w s (by omega)).DisjointWires (rData.slice 0 p.w (by omega)))
    (hhW : (rData.slice (p.w + s) (p.m - s) (by omega)).DisjointWires rW)
    (hiD : ci ∉ Set.range rD.wires) (hiXl : ci ∉ Set.range (rData.slice p.w s (by omega)).wires)
    (β : BitAssignment n)
    (hD : ∀ i, β (rD i) = 0) (hW : ∀ i, β (rW i) = 0) (hci : β ci = 0) :
    ∃ β1, runList (mbl2Stage1 p s hs f rData rD rW ci) β = some β1 ∧
      (∀ v, v ∉ Set.range rD.wires → v ∉ Set.range (rData.slice 0 p.w (by omega)).wires →
        β1 v = β v) ∧
      (∀ i, β1 (rData.slice 0 p.w (by omega) i) = β (rData.slice 0 p.w (by omega) i) +
        tableBits p.w f ((localIdx (rData.slice p.w s (by omega)) β : ℕ) +
          2 ^ s * (localIdx (rData.slice (p.w + s) (p.m - s) (by omega)) β : ℕ)) i) ∧
      ∀ q, β1 (rD q) = swTab s p.w f (localIdx (rData.slice p.w s (by omega)) β : ℕ)
        (localIdx (rData.slice (p.w + s) (p.m - s) (by omega)) β : ℕ) q := by
  set rXl := rData.slice p.w s (by omega) with hrXl
  set rXh := rData.slice (p.w + s) (p.m - s) (by omega) with hrXh
  set rY := rData.slice 0 p.w (by omega) with hrY
  set B := dataBlock s p.w rD with hBdef
  set S := swapTree ci p.w B s rXl with hS
  have hnB : ∀ {v}, v ∉ Set.range rD.wires → ∀ l, v ∉ Set.range (B l).wires :=
    fun hv _ ↦ not_mem_slice hv _ _ _
  have hlook := fun β' ↦ runList_lookupSteps (2 ^ s * p.w) rD (p.m - s) none rXh rW
    (wideTab s p.w f) hhW
    (QRegister.disjoint_comm.mp hDh) (QRegister.disjoint_comm.mp hDW)
    (fun _ ↦ ctrlNe_none _) (fun _ ↦ ctrlNe_none _) (fun _ ↦ ctrlNe_none _) β'
  set x := (localIdx rXl β : ℕ) + 2 ^ s * (localIdx rXh β : ℕ) with hx
  set β1 := writeReg β rD (wideTab s p.w f (localIdx rXh β)) with hβ1
  have h1 : runList (lookupSteps (2 ^ s * p.w) rD (p.m - s) none rXh rW (wideTab s p.w f)) β =
      some β1 := by
    rw [hlook β hW]
    simp only [hD, ctrlVal, zero_add, one_mul]
    rfl
  have hb1 : ∀ v, v ∉ Set.range rD.wires → β1 v = β v := fun v hv ↦
    writeReg_apply_of_not_mem _ _ _ _ hv
  obtain ⟨β2, h2, hfr2_B, h2B⟩ := runList_swapTree_full ci p.w B s rXl
    (fun l l' hl hl' h ↦ dataBlock_disjoint s p.w rD hl hl' h)
    (fun j ↦ hnB (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDl) j))
    hiXl (hnB hiD) β1 (by rw [hb1 _ hiD, hci])
  have hfr2 : ∀ v, v ∉ Set.range rD.wires → β2 v = β1 v := fun v hv ↦
    hfr2_B v (fun l _ ↦ hnB hv l)
  have hBj : ∀ j < 2 ^ s, ∀ i, β2 (B j i) =
      tableBits p.w f (swapSrc s (localIdx rXl β : ℕ) j + 2 ^ s * (localIdx rXh β : ℕ)) i :=
    fun j hj i ↦ by
    rw [h2B j hj i, localIdx_writeReg_of_disjoint _ _ _ hDl, hβ1,
      writeReg_wideTab_dataBlock _ _ _ _ _ _ _ (swapSrc_lt s _ j hj)]
  have hB0 : ∀ i, β2 (B 0 i) = tableBits p.w f x i := fun i ↦ by
    rw [hBj 0 (by positivity) i, swapSrc_zero s _ (localIdx rXl β).isLt]
  have hrY2 : ∀ i, β2 (rY i) = β (rY i) := fun i ↦ by
    rw [hfr2 _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDY) i),
      hb1 _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDY) i)]
  set γ : BitAssignment p.w := fun i ↦ β (rY i) + tableBits p.w f x i with hγ
  have h3 : runList (copySteps p.w (B 0) rY) β2 = some (writeReg β2 rY γ) := by
    rw [runList_copySteps p.w (B 0) rY (hDY.compose_left _)]
    congr 2
    funext i
    rw [hB0, hrY2]
  refine ⟨writeReg β2 rY γ, ?_, fun v hvD hvY ↦ ?_, fun i ↦ ?_, fun q ↦ ?_⟩
  · rw [mbl2Stage1, runList_append, runList_append, h1, Option.bind_some, ← hS, h2,
      Option.bind_some, h3]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hvY, hfr2 v hvD, hb1 v hvD]
  · exact writeReg_apply_reg β2 rY γ i
  · have hw : 0 < p.w := Nat.pos_of_ne_zero (by
      intro h
      have := q.isLt
      simp [h] at this)
    rw [writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hDY q), rD_eq_block s p.w rD q hw,
      hBj _ (Nat.div_lt_of_lt_mul (lt_of_lt_of_eq q.isLt (mul_comm _ _)))]
    rfl

theorem mbl2Stage1_ac (p : LookupParams) (s : ℕ) (hs : s ≤ p.m) (f : ℕ → ℕ)
    (rData : QRegister (p.m + p.w) n) (rD : QRegister (2 ^ s * p.w) n)
    (rW : QRegister (p.m - s) n) (ci : Wire n) :
    ac (mbl2Stage1 p s hs f rData rD rW ci) + p.w ≤ (2 ^ (p.m - s) - 1) + 2 ^ s * p.w := by
  have h1 : ac (lookupSteps (2 ^ s * p.w) rD (p.m - s) none
      (rData.slice (p.w + s) (p.m - s) (by omega)) rW (wideTab s p.w f)) ≤ 2 ^ (p.m - s) - 1 :=
    andCount_lookupSteps _ _ _ _ _ _ _
  have h2 := ac_swapTree ci p.w (dataBlock s p.w rD) s (rData.slice p.w s (by omega))
  have h4 := ac_copySteps p.w (dataBlock s p.w rD 0) (rData.slice 0 p.w (by omega))
  simp only [mbl2Stage1, ac_append]
  omega

/-- The width-1 table of parities of the mask `r` against the swapped junk content, as a
function of the full address. -/
def gTab2 (p : LookupParams) (s : ℕ) (f : ℕ → ℕ) (r : Fin (2 ^ s * p.w) → ZMod 2) (h : ℕ) : ℕ :=
  (∑ j, r j * swTab s p.w f (h % 2 ^ s) (h / 2 ^ s) j).val

theorem gTab2_bit (p : LookupParams) (s : ℕ) (f : ℕ → ℕ) (r : Fin (2 ^ s * p.w) → ZMod 2)
    (h : ℕ) : tableBits 1 (gTab2 p s f r) h 0 =
      ∑ j, r j * swTab s p.w f (h % 2 ^ s) (h / 2 ^ s) j := by
  simp only [tableBits, gTab2, Fin.val_zero, _root_.pow_zero, Nat.div_one]
  rw [ZMod.natCast_mod, ZMod.natCast_zmod_val]

/-- Stage 2 leaf: width-1 phase lookup over the full address. -/
def mbl2Leaf (p : LookupParams) (s s2 : ℕ) (hs : s ≤ p.m) (hs2 : s2 ≤ p.m)
    (data : LookupTable p) (rData : QRegister (p.m + p.w) n) {N : ℕ} (rAnc : QRegister N n)
    (hN : 2 ^ s * p.w + (p.m - s) + 1 + (2 ^ s2 * 1 + (p.m - s2) + 1) ≤ N)
    (r : Fin (2 ^ s * p.w) → ZMod 2) : DynamicCircuit Var n :=
  leafCirc p.m s2 (gTab2 p s (fTab data) r)
    ((rData.slice p.w p.m (by omega)).slice 0 s2 (by omega))
    ((rData.slice p.w p.m (by omega)).slice s2 (p.m - s2) (by omega))
    (rAnc.slice (2 ^ s * p.w + (p.m - s) + 1 + 2 ^ s2 * 1) (p.m - s2) (by omega))
    (rAnc.slice (2 ^ s * p.w + (p.m - s) + 1) (2 ^ s2 * 1) (by omega))
    (rAnc ⟨2 ^ s * p.w + (p.m - s) + 1 + 2 ^ s2 * 1 + (p.m - s2), by omega⟩)

/-- Lookup measuring the junk register right after the copy. -/
def mbl2Prog (p : LookupParams) (s s2 : ℕ) (hs : s ≤ p.m) (hs2 : s2 ≤ p.m)
    (data : LookupTable p) (rData : QRegister (p.m + p.w) n) {N : ℕ} (rAnc : QRegister N n)
    (hN : 2 ^ s * p.w + (p.m - s) + 1 + (2 ^ s2 * 1 + (p.m - s2) + 1) ≤ N) :
    DynamicCircuit Var n :=
  .seq (compileList (Var.v 0) (mbl2Stage1 p s hs (fTab data) rData
      (rAnc.slice 0 (2 ^ s * p.w) (by omega)) (rAnc.slice (2 ^ s * p.w) (p.m - s) (by omega))
      (rAnc ⟨2 ^ s * p.w + (p.m - s), by omega⟩)))
    (mbuTree (Var.v 0) (fun i ↦ rAnc.slice 0 (2 ^ s * p.w) (by omega) i)
      (mbl2Leaf p s s2 hs hs2 data rData rAnc hN) (List.finRange (2 ^ s * p.w)) (fun _ ↦ 0))

theorem mbl2Prog_count_T (p : LookupParams) (s s2 : ℕ) (hs : s ≤ p.m) (hs2 : s2 ≤ p.m)
    (data : LookupTable p) (rData : QRegister (p.m + p.w) n) {N : ℕ} (rAnc : QRegister N n)
    (hN : 2 ^ s * p.w + (p.m - s) + 1 + (2 ^ s2 * 1 + (p.m - s2) + 1) ≤ N) :
    (mbl2Prog p s s2 hs hs2 data rData rAnc hN).count PrimitiveGate.T ≤
      4 * (2 ^ (p.m - s) - 1) + 4 * (2 ^ s - 1) * p.w + ssT p.m 1 s2 := by
  have h1 := count_T_compileList (Var.v 0) (mbl2Stage1 p s hs (fTab data) rData
      (rAnc.slice 0 (2 ^ s * p.w) (by omega)) (rAnc.slice (2 ^ s * p.w) (p.m - s) (by omega))
      (rAnc ⟨2 ^ s * p.w + (p.m - s), by omega⟩))
  have h2 := mbl2Stage1_ac p s hs (fTab data) rData
      (rAnc.slice 0 (2 ^ s * p.w) (by omega)) (rAnc.slice (2 ^ s * p.w) (p.m - s) (by omega))
      (rAnc ⟨2 ^ s * p.w + (p.m - s), by omega⟩)
  have h3 : (mbuTree (Var.v 0) (fun i ↦ rAnc.slice 0 (2 ^ s * p.w) (by omega) i)
      (mbl2Leaf p s s2 hs hs2 data rData rAnc hN) (List.finRange (2 ^ s * p.w))
      (fun _ ↦ 0)).count PrimitiveGate.T ≤ ssT p.m 1 s2 :=
    mbuTree_count _ _ _ _ _ (fun q ↦ by simp) (fun q ↦ by simp)
      (fun r ↦ leafCirc_count_T _ _ hs2 _ _ _ _ _ _) _ _
  have e : ((mbl2Stage1 p s hs (fTab data) rData
      (rAnc.slice 0 (2 ^ s * p.w) (by omega)) (rAnc.slice (2 ^ s * p.w) (p.m - s) (by omega))
      (rAnc ⟨2 ^ s * p.w + (p.m - s), by omega⟩)).map Step.andCount).sum = ac (mbl2Stage1 p s hs
      (fTab data) rData
      (rAnc.slice 0 (2 ^ s * p.w) (by omega)) (rAnc.slice (2 ^ s * p.w) (p.m - s) (by omega))
      (rAnc ⟨2 ^ s * p.w + (p.m - s), by omega⟩)) := rfl
  rw [e] at h1
  have h4 : 4 * (2 ^ s - 1) * p.w + 4 * p.w = 4 * (2 ^ s * p.w) := by
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ s = k + 1 := ⟨2 ^ s - 1, by have := @Nat.one_le_two_pow s; omega⟩
    rw [hk, Nat.add_sub_cancel]
    ring
  unfold mbl2Prog
  simp only [DynamicCircuit.count]
  omega

theorem mbl2Prog_count_TOFF (p : LookupParams) (s s2 : ℕ) (hs : s ≤ p.m) (hs2 : s2 ≤ p.m)
    (data : LookupTable p) (rData : QRegister (p.m + p.w) n) {N : ℕ} (rAnc : QRegister N n)
    (hN : 2 ^ s * p.w + (p.m - s) + 1 + (2 ^ s2 * 1 + (p.m - s2) + 1) ≤ N) :
    (mbl2Prog p s s2 hs hs2 data rData rAnc hN).count PrimitiveGate.TOFF = 0 := by
  have h3 := mbuTree_count (Var.v 0) (fun i ↦ rAnc.slice 0 (2 ^ s * p.w) (by omega) i)
      (mbl2Leaf p s s2 hs hs2 data rData rAnc hN) PrimitiveGate.TOFF 0
      (fun q ↦ by simp) (fun q ↦ by simp)
      (fun r ↦ (leafCirc_count_TOFF _ _ _ _ _ _ _ _).le) (List.finRange (2 ^ s * p.w))
      (fun _ ↦ 0)
  have h1 := count_TOFF_compileList (Var.v 0) (mbl2Stage1 p s hs (fTab data) rData
      (rAnc.slice 0 (2 ^ s * p.w) (by omega)) (rAnc.slice (2 ^ s * p.w) (p.m - s) (by omega))
      (rAnc ⟨2 ^ s * p.w + (p.m - s), by omega⟩))
  unfold mbl2Prog
  simp only [DynamicCircuit.count]
  omega

theorem split_mod_div (L H s : ℕ) (hL : L < 2 ^ s) :
    (L + 2 ^ s * H) % 2 ^ s = L ∧ (L + 2 ^ s * H) / 2 ^ s = H := by
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hL]
  · rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hL, zero_add]

theorem mbl2Prog_realizes (p : LookupParams) (s s2 : ℕ) (hs : s ≤ p.m) (hs2 : s2 ≤ p.m)
    (data : LookupTable p) (rData : QRegister (p.m + p.w) n) {N : ℕ} (rAnc : QRegister N n)
    (hN : 2 ^ s * p.w + (p.m - s) + 1 + (2 ^ s2 * 1 + (p.m - s2) + 1) ≤ N)
    (hd : rData.DisjointWires rAnc) (V : Set (Fin (2 ^ (p.m + p.w)))) :
    RealizesCleanSubroutineOnEncoding rData rAnc hd V (tableXorPerm data.extend)
      (mbl2Prog p s s2 hs hs2 data rData rAnc hN).compile := by
  haveI : NeZero (2 ^ n) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hDA : ∀ {a b : ℕ} (r : QRegister a (p.m + p.w)) (r' : QRegister b N),
      (rAnc.compose r').DisjointWires (rData.compose r) := fun _ _ ↦
    QRegister.disjoint_comm.mp ((hd.compose_left _).compose_right _)
  have hXA : ∀ {a b : ℕ} (r : QRegister a p.m) (r' : QRegister b N),
      (rAnc.compose r').DisjointWires ((rData.slice p.w p.m (by omega)).compose r) :=
    fun r r' ↦ QRegister.disjoint_comm.mp
      (((hd.compose_left (QRegister.block p.w p.m (by omega))).compose_left r).compose_right r')
  have hx : ∀ γ : BitAssignment n, (localIdx (addrReg p rData) γ : ℕ) =
      (localIdx (rData.slice p.w s (by omega)) γ : ℕ) +
        2 ^ s * (localIdx (rData.slice (p.w + s) (p.m - s) (by omega)) γ : ℕ) := fun γ ↦ by
    rw [localIdx_val_split (addrReg p rData) s (p.m - s) (by omega)]
    simp only [localIdx_slice_slice, add_zero]
  have hxh : ∀ γ : BitAssignment n,
      (localIdx ((rData.slice p.w p.m (by omega)).slice 0 s2 (by omega)) γ : ℕ) +
        2 ^ s2 * (localIdx ((rData.slice p.w p.m (by omega)).slice s2
          (p.m - s2) (by omega)) γ : ℕ) =
        (localIdx (rData.slice p.w p.m (by omega)) γ : ℕ) := fun γ ↦
    (localIdx_val_split (rData.slice p.w p.m (by omega)) s2 (p.m - s2)
      (by omega) γ).symm
  have hDl : (rAnc.slice 0 (2 ^ s * p.w) (by omega)).DisjointWires
      (rData.slice p.w s (by omega)) := hDA _ _
  have hDh : (rAnc.slice 0 (2 ^ s * p.w) (by omega)).DisjointWires
      (rData.slice (p.w + s) (p.m - s) (by omega)) := hDA _ _
  obtain ⟨R1, hK1, hR1, -⟩ := exists_lowerKraus_compileList (Var.v 0) (mbl2Stage1 p s hs (fTab data)
    rData (rAnc.slice 0 (2 ^ s * p.w) (by omega)) (rAnc.slice (2 ^ s * p.w) (p.m - s) (by omega))
    (rAnc ⟨2 ^ s * p.w + (p.m - s), by omega⟩))
  obtain ⟨R2, hK2, hR2⟩ := mbuTree_kraus (Var.v 0) (fun i ↦ rAnc.slice 0 (2 ^ s * p.w) (by omega) i)
    (mbl2Leaf p s s2 hs hs2 data rData rAnc hN)
    (fun i γ ↦ swTab s p.w (fTab data) (localIdx (rData.slice p.w s (by omega)) γ : ℕ)
      (localIdx (rData.slice (p.w + s) (p.m - s) (by omega)) γ : ℕ) i)
    (fun γ ↦ ∀ k : Fin N, 2 ^ s * p.w + (p.m - s) + 1 ≤ k.val → γ (rAnc k) = 0)
    (fun i j h ↦ (rAnc.slice 0 (2 ^ s * p.w) (by omega)).wires.injective h)
    (fun γ i a h k hk ↦ by
      rw [update_of_ne]
      · exact h k hk
      · intro e
        have := rAnc.wires.injective e
        have h2 : 0 + (i : ℕ) = (k : ℕ) := (congrArg Fin.val this).symm
        have h3 := i.isLt
        omega)
    (fun γ i j a ↦ by
      simp only [localIdx_update_of_not_mem _ γ (not_mem_of_disjoint hDl i) a,
        localIdx_update_of_not_mem _ γ (not_mem_of_disjoint hDh i) a])
    (fun r ↦ by
      obtain ⟨L, hL, hLk⟩ := leafCirc_kraus p.m s2 (gTab2 p s (fTab data) r)
        ((rData.slice p.w p.m (by omega)).slice 0 s2 (by omega))
        ((rData.slice p.w p.m (by omega)).slice s2 (p.m - s2) (by omega))
        (rAnc.slice (2 ^ s * p.w + (p.m - s) + 1 + 2 ^ s2 * 1) (p.m - s2) (by omega))
        (rAnc.slice (2 ^ s * p.w + (p.m - s) + 1) (2 ^ s2 * 1) (by omega))
        (rAnc ⟨2 ^ s * p.w + (p.m - s) + 1 + 2 ^ s2 * 1 + (p.m - s2), by omega⟩)
        (hXA _ _) (hXA _ _)
        (QRegister.slice_disjoint_of_le rAnc _ _ _ _ (by omega) (by omega) (by omega))
        (QRegister.disjoint_comm.mp (hXA _ _))
        (apply_not_mem_slice rAnc _ (2 ^ s * p.w + (p.m - s) + 1) _ (by omega) (Or.inr (by simp)))
        (fun ⟨i, h⟩ ↦ ((hd.compose_left (QRegister.block p.w p.m (by omega))).compose_left
          (QRegister.block 0 s2 (by omega))).ne i _ h)
      refine ⟨L, hL, fun γ hγ ↦ ?_⟩
      have hD0 : ∀ i : Fin (2 ^ s2 * 1), γ (rAnc.slice (2 ^ s * p.w + (p.m - s) + 1)
          (2 ^ s2 * 1) (by omega) i) = 0 := fun i ↦ by
        have := i.isLt
        exact hγ ⟨2 ^ s * p.w + (p.m - s) + 1 + i, by omega⟩ (Nat.le_add_right _ _)
      have hW0 : ∀ i : Fin (p.m - s2), γ (rAnc.slice (2 ^ s * p.w + (p.m - s) + 1 +
          2 ^ s2 * 1) (p.m - s2) (by omega) i) = 0 := fun i ↦ by
        have := i.isLt
        exact hγ ⟨2 ^ s * p.w + (p.m - s) + 1 + 2 ^ s2 * 1 + i, by omega⟩
          (by change _ ≤ 2 ^ s * p.w + (p.m - s) + 1 + 2 ^ s2 * 1 + (i : ℕ); omega)
      have hc0 : γ (rAnc ⟨2 ^ s * p.w + (p.m - s) + 1 + 2 ^ s2 * 1 + (p.m - s2),
          by omega⟩) = 0 :=
        hγ _ (by change _ ≤ 2 ^ s * p.w + (p.m - s) + 1 + 2 ^ s2 * 1 + (p.m - s2); omega)
      rw [hLk γ hD0 hW0 hc0, hxh γ, gTab2_bit]
      have hx' : (localIdx (rData.slice p.w p.m (by omega)) γ : ℕ) =
          (localIdx (rData.slice p.w s (by omega)) γ : ℕ) +
            2 ^ s * (localIdx (rData.slice (p.w + s) (p.m - s) (by omega)) γ : ℕ) := hx γ
      obtain ⟨hm, hdv⟩ := split_mod_div _ (localIdx (rData.slice (p.w + s) (p.m - s)
        (by omega)) γ : ℕ) s (localIdx (rData.slice p.w s (by omega)) γ).isLt
      rw [hx', hm, hdv])
    (List.finRange (2 ^ s * p.w)) (List.nodup_finRange _) (fun _ ↦ 0)
  refine realizesOnEncoding_of_lowerKraus rData rAnc hd V _ (hK1.qSeq hK2) fun β h0 _ ↦ ?_
  have hclean := eq_zero_of_localIdx_eq_zero rAnc β h0
  have hD0 : ∀ i, β (rAnc.slice 0 (2 ^ s * p.w) (by omega) i) = 0 := fun _ ↦ hclean _
  have hW0 : ∀ i, β (rAnc.slice (2 ^ s * p.w) (p.m - s) (by omega) i) = 0 := fun _ ↦ hclean _
  have hlYs : (rData.slice p.w s (by omega)).DisjointWires (rData.slice 0 p.w (by omega)) :=
    QRegister.disjoint_comm.mp
      (QRegister.slice_disjoint_of_le rData _ _ _ _ (by omega) (by omega) (by omega))
  have hhYs : (rData.slice (p.w + s) (p.m - s) (by omega)).DisjointWires
      (rData.slice 0 p.w (by omega)) :=
    QRegister.disjoint_comm.mp
      (QRegister.slice_disjoint_of_le rData _ _ _ _ (by omega) (by omega) (by omega))
  obtain ⟨β1, hrun, hfr, hY, hDc⟩ := runList_mbl2Stage1 p s hs (fTab data) rData
    (rAnc.slice 0 (2 ^ s * p.w) (by omega))
    (rAnc.slice (2 ^ s * p.w) (p.m - s) (by omega)) (rAnc ⟨2 ^ s * p.w + (p.m - s), by omega⟩)
    hDl hDh
    (QRegister.slice_disjoint_of_le rAnc _ _ _ _ (by omega) (by omega) (by omega)) (hDA _ _)
    hlYs
    (QRegister.disjoint_comm.mp (hDA _ _))
    (apply_not_mem_slice rAnc _ 0 _ (by omega) (Or.inr (by simp)))
    (fun ⟨_, h⟩ ↦ hd.ne _ _ h)
    β hD0 hW0 (hclean _)
  set rD := rAnc.slice 0 (2 ^ s * p.w) (by omega) with hrD
  set rXl := rData.slice p.w s (by omega) with hrXl
  set rXh := rData.slice (p.w + s) (p.m - s) (by omega) with hrXh
  set rY := rData.slice 0 p.w (by omega) with hrY
  have hDY : rD.DisjointWires rY := hDA _ _
  have hYA : rY.DisjointWires rAnc := hd.compose_left _
  have hG : ∀ k : Fin N, 2 ^ s * p.w + (p.m - s) + 1 ≤ k.val → β1 (rAnc k) = 0 := by
    intro k hk
    rw [hfr _ (apply_not_mem_slice rAnc k 0 _ (by omega) (Or.inr (by omega)))
      (fun ⟨i, h⟩ ↦ hYA.ne i k h)]
    exact hclean k
  have hloc : ∀ {a : ℕ} (r : QRegister a n), (∀ i, r i ∉ Set.range rD.wires) →
      (∀ i, r i ∉ Set.range rY.wires) → localIdx r β1 = localIdx r β := fun r h1 h2 ↦ by
    simp only [localIdx]
    congr 1
    funext i
    exact hfr _ (h1 i) (h2 i)
  have hl1 : localIdx rXl β1 = localIdx rXl β :=
    hloc _ (fun i ↦ not_mem_of_disjoint (QRegister.disjoint_comm.mp hDl) i)
      (fun i ↦ not_mem_of_disjoint hlYs i)
  have hl2 : localIdx rXh β1 = localIdx rXh β :=
    hloc _ (fun i ↦ not_mem_of_disjoint (QRegister.disjoint_comm.mp hDh) i)
      (fun i ↦ not_mem_of_disjoint hhYs i)
  have hcond : ∀ i ∈ List.finRange (2 ^ s * p.w),
      β1 (rD i) = swTab s p.w (fTab data) (localIdx rXl β1 : ℕ) (localIdx rXh β1 : ℕ) i := by
    intro i _
    rw [hl1, hl2]
    exact hDc i
  rw [← Matrix.mulVec_mulVec, hR1 _ _ hrun, hR2 _ hG, if_pos hcond]
  simp only [zero_mul, Finset.sum_const_zero, bitSign, if_true, one_smul]
  rw [MblImpl.zeroL_finRange', ← target_xor_eq data rData β]
  congr 1
  funext v
  by_cases hvD : v ∈ Set.range rD.wires
  · obtain ⟨i, rfl⟩ := hvD
    rw [writeReg_apply_reg, writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hDY i), hD0 i]
  · by_cases hvY : v ∈ Set.range rY.wires
    · obtain ⟨i, rfl⟩ := hvY
      rw [writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hDY) i),
        hY i, writeReg_apply_reg, ← hx β]
      exact congrArg (β (rY i) + ·) (congrFun (hbits data _ (localIdx (addrReg p rData) β).isLt) i)
    · rw [writeReg_apply_of_not_mem _ _ _ _ hvD, writeReg_apply_of_not_mem _ _ _ _ hvY,
        hfr v hvD hvY]

/-- `T` count of the lookup that measures the junk register right after the copy. -/
def mbl2T (m w s s2 : ℕ) : ℕ := 4 * (2 ^ (m - s) - 1) + 4 * (2 ^ s - 1) * w + ssT m 1 s2

/-- Second swap depth: best select-swap depth for the width-1 phase lookup over the full
address in the remaining budget. -/
def mbl2S2 (m w a s : ℕ) : ℕ := ssBest m 1 (a - ssA m w s)

/-- Clean ancillas of the lookup that measures the junk register right after the copy. -/
def mbl2A (m w s s2 : ℕ) : ℕ := ssA m w s + ssA m 1 s2

/-- Swap depth in `0..m` minimizing `mbl2T` among those with `mbl2A ≤ a` (ties to the smaller
`s`). -/
def mbl2Best (m w a : ℕ) : ℕ :=
  (List.range (m + 1)).foldl
    (fun b s ↦ if mbl2A m w s (mbl2S2 m w a s) ≤ a ∧
        (a < mbl2A m w b (mbl2S2 m w a b) ∨
          mbl2T m w s (mbl2S2 m w a s) < mbl2T m w b (mbl2S2 m w a b))
      then s else b) 0

/-- Ancillas of the previous budgeted lookup (measurement cleanup after the unswap, or
select-swap, or unary). -/
def curAnc (m w a : ℕ) : ℕ :=
  if MblImpl.mblCond m w a then
    MblImpl.mblA m w (MblImpl.mblBest m w a) (MblImpl.mblS2 m w a (MblImpl.mblBest m w a))
  else SelectSwapImpl.ssAnc m w a

/-- `T` cost of the previous budgeted lookup. -/
def curT (m w a : ℕ) : ℕ :=
  if MblImpl.mblCond m w a then
    MblImpl.mblT m w (MblImpl.mblBest m w a) (MblImpl.mblS2 m w a (MblImpl.mblBest m w a))
  else MbuImpl.oldTCost m w a

/-- The previous budgeted lookup program. -/
def curProg {n : ℕ} (p : BudgetLookupParams) (data : LookupTable p.toLookupParams)
    (rData : QRegister (p.m + p.w) n) (rAnc : QRegister (curAnc p.m p.w p.a) n) :
    DynamicCircuit Var n :=
  if h : MblImpl.mblCond p.m p.w p.a then
    MblImpl.mblProg p.toLookupParams (MblImpl.mblBest p.m p.w p.a)
      (MblImpl.mblS2 p.m p.w p.a (MblImpl.mblBest p.m p.w p.a)) h.1 h.2.1 data rData rAnc
      (le_of_eq (if_pos h).symm)
  else
    MbuImpl.oldProg p data rData (SelectSwapImpl.castReg (if_neg h) rAnc)

/-- Use the lookup that measures the junk register right after the copy. -/
def mbl2Cond (m w a : ℕ) : Prop :=
  mbl2Best m w a ≤ m ∧ mbl2S2 m w a (mbl2Best m w a) ≤ m ∧
    mbl2A m w (mbl2Best m w a) (mbl2S2 m w a (mbl2Best m w a)) ≤ a ∧
    mbl2T m w (mbl2Best m w a) (mbl2S2 m w a (mbl2Best m w a)) < curT m w a

instance (m w a : ℕ) : Decidable (mbl2Cond m w a) := by unfold mbl2Cond; infer_instance

theorem curProg_realizes (p : BudgetLookupParams) (data : LookupTable p.toLookupParams)
    {n : ℕ} (rData : QRegister (p.m + p.w) n) (rAnc : QRegister (curAnc p.m p.w p.a) n)
    (hdisj : rData.DisjointWires rAnc) (V : Set (Fin (2 ^ (p.m + p.w)))) :
    RealizesCleanSubroutineOnEncoding rData rAnc hdisj V
      (tableXorPerm data.extend) (curProg p data rData rAnc).compile := by
  by_cases h : MblImpl.mblCond p.m p.w p.a
  · unfold curProg
    rw [dif_pos h]
    exact MblImpl.mblProg_realizes p.toLookupParams _ _ h.1 h.2.1 data rData rAnc _ hdisj _
  · unfold curProg
    rw [dif_neg h]
    exact MblImpl.oldProgL_realizes_cast p data rData (if_neg h) rAnc hdisj _

theorem curProg_realizes_cast (p : BudgetLookupParams) (data : LookupTable p.toLookupParams)
    {n : ℕ} (rData : QRegister (p.m + p.w) n) {N : ℕ} (hN : N = curAnc p.m p.w p.a)
    (rAnc : QRegister N n) (hdisj : rData.DisjointWires rAnc)
    (V : Set (Fin (2 ^ (p.m + p.w)))) :
    RealizesCleanSubroutineOnEncoding rData rAnc hdisj V
      (tableXorPerm data.extend)
      (curProg p data rData (SelectSwapImpl.castReg hN rAnc)).compile := by
  subst hN
  exact curProg_realizes p data rData rAnc hdisj V

theorem curProg_count (p : BudgetLookupParams) (hp : p.Valid)
    (data : LookupTable p.toLookupParams) {n : ℕ} (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (curAnc p.m p.w p.a) n) :
    curAnc p.m p.w p.a ≤ p.a ∧
      (curProg p data rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (curProg p data rData rAnc).count PrimitiveGate.T ≤ curT p.m p.w p.a := by
  by_cases h : MblImpl.mblCond p.m p.w p.a
  · refine ⟨?_, ?_, ?_⟩
    · unfold curAnc
      rw [if_pos h]
      exact h.2.2.1
    · unfold curProg
      rw [dif_pos h]
      exact MblImpl.mblProg_count_TOFF p.toLookupParams _ _ h.1 h.2.1 data rData rAnc _
    · unfold curProg curT
      rw [dif_pos h, if_pos h]
      exact MblImpl.mblProg_count_T p.toLookupParams _ _ h.1 h.2.1 data rData rAnc _
  · refine ⟨?_, ?_, ?_⟩
    · unfold curAnc
      rw [if_neg h]
      exact MbuImpl.oldAnc_le p hp
    · unfold curProg
      rw [dif_neg h]
      exact (MbuImpl.oldProg_count p data rData _).1
    · unfold curProg curT
      rw [dif_neg h]
      refine (MbuImpl.oldProg_count p data rData _).2.trans (le_of_eq ?_)
      rw [if_neg h]

end Mbl2Impl


/-- Number of clean ancilla qubits `qromBudgetLookupProgram` uses. -/
def qromBudgetLookupAncillas (p : BudgetLookupParams) : ℕ :=
  if Mbl2Impl.mbl2Cond p.m p.w p.a then
    Mbl2Impl.mbl2A p.m p.w (Mbl2Impl.mbl2Best p.m p.w p.a)
      (Mbl2Impl.mbl2S2 p.m p.w p.a (Mbl2Impl.mbl2Best p.m p.w p.a))
  else Mbl2Impl.curAnc p.m p.w p.a

/-- Budgeted lookup circuit for table `data` on the `p.m + p.w` data wires `rData` (`p.w`
target wires followed by `p.m` address wires) and `qromBudgetLookupAncillas p` clean ancilla
wires `rAnc`. -/
def qromBudgetLookupProgram {n : ℕ} (p : BudgetLookupParams) (data : LookupTable p.toLookupParams)
    (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromBudgetLookupAncillas p) n) : DynamicCircuit Var n :=
  if h : Mbl2Impl.mbl2Cond p.m p.w p.a then
    Mbl2Impl.mbl2Prog p.toLookupParams (Mbl2Impl.mbl2Best p.m p.w p.a)
      (Mbl2Impl.mbl2S2 p.m p.w p.a (Mbl2Impl.mbl2Best p.m p.w p.a)) h.1 h.2.1 data rData rAnc
      (le_of_eq (if_pos h).symm)
  else
    Mbl2Impl.curProg p data rData (SelectSwapImpl.castReg (if_neg h) rAnc)

/-- For valid sizes and budget and every table, `qromBudgetLookupProgram` realizes
`|x⟩|b⟩ ↦ |x⟩|b ⊕ data(x)⟩` on every address `x < L` and every target `b`, as an exact clean
subroutine across all disjoint register placements. -/
theorem qromBudgetLookup_correctness (p : BudgetLookupParams) (hp : p.Valid)
    (data : LookupTable p.toLookupParams) {n : ℕ} (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromBudgetLookupAncillas p) n) (hdisj : rData.DisjointWires rAnc) :
    RealizesCleanSubroutineOnEncoding rData rAnc hdisj (lookupValidInputs p.toLookupParams)
      (tableXorPerm data.extend) (qromBudgetLookupProgram p data rData rAnc).compile := by
  by_cases h : Mbl2Impl.mbl2Cond p.m p.w p.a
  · unfold qromBudgetLookupProgram
    rw [dif_pos h]
    exact Mbl2Impl.mbl2Prog_realizes p.toLookupParams _ _ h.1 h.2.1 data rData rAnc _ hdisj _
  · unfold qromBudgetLookupProgram
    rw [dif_neg h]
    exact Mbl2Impl.curProg_realizes_cast p data rData (if_neg h) rAnc hdisj _

/-- Claimed `T` count of the budgeted lookup, as a function of the sizes and the budget. -/
def qromBudgetLookupTCost (p : BudgetLookupParams) : ℕ :=
  if Mbl2Impl.mbl2Cond p.m p.w p.a then
    Mbl2Impl.mbl2T p.m p.w (Mbl2Impl.mbl2Best p.m p.w p.a)
      (Mbl2Impl.mbl2S2 p.m p.w p.a (Mbl2Impl.mbl2Best p.m p.w p.a))
  else Mbl2Impl.curT p.m p.w p.a

/-- For valid sizes and budget, every table and every placement, the budgeted lookup uses at
most `p.a` clean ancillas, no `TOFF` gates and at most `qromBudgetLookupTCost p` `T` gates. -/
theorem qromBudgetLookup_t_cost (p : BudgetLookupParams) (hp : p.Valid)
    (data : LookupTable p.toLookupParams) {n : ℕ} (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromBudgetLookupAncillas p) n) :
    qromBudgetLookupAncillas p ≤ p.a ∧
      (qromBudgetLookupProgram p data rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (qromBudgetLookupProgram p data rData rAnc).count PrimitiveGate.T ≤
        qromBudgetLookupTCost p := by
  by_cases h : Mbl2Impl.mbl2Cond p.m p.w p.a
  · refine ⟨?_, ?_, ?_⟩
    · unfold qromBudgetLookupAncillas
      rw [if_pos h]
      exact h.2.2.1
    · unfold qromBudgetLookupProgram
      rw [dif_pos h]
      exact Mbl2Impl.mbl2Prog_count_TOFF p.toLookupParams _ _ h.1 h.2.1 data rData rAnc _
    · unfold qromBudgetLookupProgram qromBudgetLookupTCost
      rw [dif_pos h, if_pos h]
      exact Mbl2Impl.mbl2Prog_count_T p.toLookupParams _ _ h.1 h.2.1 data rData rAnc _
  · have hc := Mbl2Impl.curProg_count p hp data rData (SelectSwapImpl.castReg (if_neg h) rAnc)
    refine ⟨?_, ?_, ?_⟩
    · unfold qromBudgetLookupAncillas
      rw [if_neg h]
      exact hc.1
    · unfold qromBudgetLookupProgram
      rw [dif_neg h]
      exact hc.2.1
    · unfold qromBudgetLookupProgram qromBudgetLookupTCost
      rw [dif_neg h]
      refine hc.2.2.trans (le_of_eq ?_)
      rw [if_neg h]

/-- Claimed bound on `T count * (m + w + a)` for the budgeted lookup at
`BudgetLookupParams.l1024w32a256`: `1900 * (10 + 32 + 256) = 566200`. -/
def qromBudgetLookupL1024W32A256ConstCost : ℕ := 566200

/-- At `BudgetLookupParams.l1024w32a256`, for every table and every placement, the budgeted
lookup uses at most `256` clean ancillas, no `TOFF` gates and has
`T count * (m + w + a) ≤ qromBudgetLookupL1024W32A256ConstCost`, where `m + w + a = 298` is the
declared width. -/
theorem qromBudgetLookup_l1024w32a256_const_cost
    (data : LookupTable BudgetLookupParams.l1024w32a256.toLookupParams) {n : ℕ}
    (rData : QRegister (BudgetLookupParams.l1024w32a256.m + BudgetLookupParams.l1024w32a256.w) n)
    (rAnc : QRegister (qromBudgetLookupAncillas .l1024w32a256) n) :
    qromBudgetLookupAncillas .l1024w32a256 ≤ BudgetLookupParams.l1024w32a256.a ∧
      (qromBudgetLookupProgram .l1024w32a256 data rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (qromBudgetLookupProgram .l1024w32a256 data rData rAnc).count PrimitiveGate.T *
          (BudgetLookupParams.l1024w32a256.m + BudgetLookupParams.l1024w32a256.w +
            BudgetLookupParams.l1024w32a256.a) ≤
        qromBudgetLookupL1024W32A256ConstCost := by
  have hv : BudgetLookupParams.Valid .l1024w32a256 := by
    unfold BudgetLookupParams.Valid LookupParams.Valid
    decide
  have h := qromBudgetLookup_t_cost .l1024w32a256 hv data rData rAnc
  have hc : qromBudgetLookupTCost .l1024w32a256 = 1900 := by decide
  have ha : qromBudgetLookupAncillas .l1024w32a256 = 175 := by decide
  refine ⟨by rw [ha]; decide, h.2.1, ?_⟩
  calc _ ≤ qromBudgetLookupTCost .l1024w32a256 * _ := Nat.mul_le_mul_right _ h.2.2
    _ ≤ _ := by rw [hc]; decide


/-- Number of clean ancilla qubits `qromBudgetUnlookupProgram` uses. -/
def qromBudgetUnlookupAncillas (p : BudgetLookupParams) : ℕ :=
  if MbuImpl.mbuCond p.m p.w p.a then
    SelectSwapImpl.ssA p.m 1 (SelectSwapImpl.ssBest p.m 1 p.a)
  else SelectSwapImpl.ssAnc p.m p.w p.a

/-- Budgeted unlookup circuit for table `data` on the `p.m + p.w` data wires `rData` and
`qromBudgetUnlookupAncillas p` clean ancilla wires `rAnc`. When the measurement-based variant is
cheaper it measures the `p.w` target wires in the Hadamard basis and applies a width-one phase
lookup per outcome pattern; otherwise it reruns the select-swap lookup. -/
def qromBudgetUnlookupProgram {n : ℕ} (p : BudgetLookupParams)
    (data : LookupTable p.toLookupParams) (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromBudgetUnlookupAncillas p) n) : DynamicCircuit Var n :=
  if h : MbuImpl.mbuCond p.m p.w p.a then
    MbuImpl.mbuProg p.toLookupParams (SelectSwapImpl.ssBest p.m 1 p.a) h.1 data rData rAnc
      (le_of_eq (if_pos h).symm)
  else
    MbuImpl.oldProg p data rData (SelectSwapImpl.castReg (if_neg h) rAnc)

/-- For valid sizes and budget and every table, `qromBudgetUnlookupProgram` realizes
`|x⟩|data(x)⟩ ↦ |x⟩|0⟩` on every address `x < L`, as an exact clean subroutine across all
disjoint register placements. Inputs whose target differs from `data(x)` are unconstrained. -/
theorem qromBudgetUnlookup_correctness (p : BudgetLookupParams) (hp : p.Valid)
    (data : LookupTable p.toLookupParams) {n : ℕ} (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromBudgetUnlookupAncillas p) n) (hdisj : rData.DisjointWires rAnc) :
    RealizesCleanSubroutineOnEncoding rData rAnc hdisj (unlookupValidInputs data)
      (tableXorPerm data.extend) (qromBudgetUnlookupProgram p data rData rAnc).compile := by
  by_cases h : MbuImpl.mbuCond p.m p.w p.a
  · unfold qromBudgetUnlookupProgram
    rw [dif_pos h]
    exact MbuImpl.mbuProg_realizes p.toLookupParams _ h.1 data rData rAnc _ hdisj
  · unfold qromBudgetUnlookupProgram
    rw [dif_neg h]
    exact MbuImpl.oldProg_realizes_cast p data rData (if_neg h) rAnc hdisj

/-- Claimed `T` count of the budgeted unlookup, as a function of the sizes and the budget. -/
def qromBudgetUnlookupTCost (p : BudgetLookupParams) : ℕ :=
  if MbuImpl.mbuCond p.m p.w p.a then
    SelectSwapImpl.ssT p.m 1 (SelectSwapImpl.ssBest p.m 1 p.a)
  else MbuImpl.oldTCost p.m p.w p.a

/-- For valid sizes and budget, every table and every placement, the budgeted unlookup uses at
most `p.a` clean ancillas, no `TOFF` gates and at most `qromBudgetUnlookupTCost p` `T` gates.
Classically controlled branches count as the larger branch. -/
theorem qromBudgetUnlookup_t_cost (p : BudgetLookupParams) (hp : p.Valid)
    (data : LookupTable p.toLookupParams) {n : ℕ} (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromBudgetUnlookupAncillas p) n) :
    qromBudgetUnlookupAncillas p ≤ p.a ∧
      (qromBudgetUnlookupProgram p data rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (qromBudgetUnlookupProgram p data rData rAnc).count PrimitiveGate.T ≤
        qromBudgetUnlookupTCost p := by
  by_cases h : MbuImpl.mbuCond p.m p.w p.a
  · refine ⟨?_, ?_, ?_⟩
    · unfold qromBudgetUnlookupAncillas
      rw [if_pos h]
      exact h.2.1
    · unfold qromBudgetUnlookupProgram
      rw [dif_pos h]
      exact MbuImpl.mbuProg_count_TOFF p.toLookupParams _ h.1 data rData rAnc _
    · unfold qromBudgetUnlookupProgram qromBudgetUnlookupTCost
      rw [dif_pos h, if_pos h]
      exact MbuImpl.mbuProg_count_T p.toLookupParams _ h.1 data rData rAnc _
  · refine ⟨?_, ?_, ?_⟩
    · unfold qromBudgetUnlookupAncillas
      rw [if_neg h]
      exact MbuImpl.oldAnc_le p hp
    · unfold qromBudgetUnlookupProgram
      rw [dif_neg h]
      exact (MbuImpl.oldProg_count p data rData _).1
    · unfold qromBudgetUnlookupProgram qromBudgetUnlookupTCost
      rw [dif_neg h]
      refine (MbuImpl.oldProg_count p data rData _).2.trans (le_of_eq ?_)
      rw [if_neg h]

/-- Claimed bound on `T count * (m + w + a)` for the budgeted unlookup at
`BudgetLookupParams.l1024w32a256`: `496 * (10 + 32 + 256) = 147808`. -/
def qromBudgetUnlookupL1024W32A256ConstCost : ℕ := 147808

/-- At `BudgetLookupParams.l1024w32a256`, for every table and every placement, the budgeted
unlookup uses at most `256` clean ancillas, no `TOFF` gates and has
`T count * (m + w + a) ≤ qromBudgetUnlookupL1024W32A256ConstCost`. -/
theorem qromBudgetUnlookup_l1024w32a256_const_cost
    (data : LookupTable BudgetLookupParams.l1024w32a256.toLookupParams) {n : ℕ}
    (rData : QRegister (BudgetLookupParams.l1024w32a256.m + BudgetLookupParams.l1024w32a256.w) n)
    (rAnc : QRegister (qromBudgetUnlookupAncillas .l1024w32a256) n) :
    qromBudgetUnlookupAncillas .l1024w32a256 ≤ BudgetLookupParams.l1024w32a256.a ∧
      (qromBudgetUnlookupProgram .l1024w32a256 data rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (qromBudgetUnlookupProgram .l1024w32a256 data rData rAnc).count PrimitiveGate.T *
          (BudgetLookupParams.l1024w32a256.m + BudgetLookupParams.l1024w32a256.w +
            BudgetLookupParams.l1024w32a256.a) ≤
        qromBudgetUnlookupL1024W32A256ConstCost := by
  have hv : BudgetLookupParams.Valid .l1024w32a256 := by
    unfold BudgetLookupParams.Valid LookupParams.Valid
    decide
  have h := qromBudgetUnlookup_t_cost .l1024w32a256 hv data rData rAnc
  have hc : qromBudgetUnlookupTCost .l1024w32a256 = 496 := by decide
  have ha : qromBudgetUnlookupAncillas .l1024w32a256 = 38 := by decide
  refine ⟨by rw [ha]; decide, h.2.1, ?_⟩
  calc _ ≤ qromBudgetUnlookupTCost .l1024w32a256 * _ := Nat.mul_le_mul_right _ h.2.2
    _ ≤ _ := by rw [hc]; decide

end QuantumComputation.Specs
