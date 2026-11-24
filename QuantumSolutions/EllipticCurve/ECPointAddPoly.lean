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

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import QuantumComputation.Circuits.DynamicCircuit
public import QuantumComputation.Circuits.ResourceCounting
public import QuantumComputation.QuantumHoareLogic.CleanAncilla

/-!
# Polynomial baseline for the affine `ecAdd` specification

The first part of this file is the machinery of `ECPointAddProjPoly.lean` (field registers,
multiply-accumulate programs, the projective mixed-addition formula), unchanged.

Inversion-free mixed addition in homogeneous projective coordinates, as a straight-line program
of multiply-accumulate operations `acc ← acc + a * b mod p` on field registers, each compiled to
the schoolbook multiplier `FieldMulCore.mulSteps`, followed by a copy of the result and the
inverse of the computation.

Self-contained against `formal-quantum-computation` main: the files it needs from the published
`Arcsin` solution are copied in below, between the GOOGLE-DERIVED markers (Copyright 2026 Google
LLC, Apache-2.0).
-/

@[expose] public section

/-!
## BEGIN GOOGLE-DERIVED

The text between the BEGIN and END markers is copied unchanged (file headers and imports removed)
from `QuantumComputationDiscoveries/Primitives/Arcsin/Solution/{LowerKraus,StepSemantics,
EqualTableAdd}.lean` on the `discoveries` branch of `google-deepmind/formal-quantum-computation`
(commit a88de8f), Copyright 2026 Google LLC, licensed under the Apache License, Version 2.0.
-/

-- ---- from QuantumComputationDiscoveries/Primitives/Arcsin/Solution/LowerKraus.lean (discoveries a88de8f) ----
namespace QuantumComputation.Specs

namespace ArcsinImpl

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


end ArcsinImpl

end QuantumComputation.Specs

-- ---- from QuantumComputationDiscoveries/Primitives/Arcsin/Solution/StepSemantics.lean (discoveries a88de8f) ----
namespace QuantumComputation.Specs

namespace ArcsinImpl

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


end ArcsinImpl

end QuantumComputation.Specs

-- ---- from QuantumComputationDiscoveries/Primitives/Arcsin/Solution/EqualTableAdd.lean (discoveries a88de8f) ----
namespace QuantumComputation.Specs

namespace ArcsinImpl

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


end ArcsinImpl

end QuantumComputation.Specs

/-!
## END GOOGLE-DERIVED
-/

namespace QuantumComputation.Specs

namespace OnEncodingBridge

open Operator Matrix QProg Function ArcsinImpl
open scoped Matrix ComplexOrder MatrixOrder

variable {Var : Type} {n k m : ℕ}

/-- A permutation unitary maps a basis state to a basis state. -/
theorem permutationUnitary_mulVec_basisState {d : ℕ} (e : Equiv.Perm (Fin d)) (j : Fin d) :
    (permutationUnitary e).1 *ᵥ basisState j = basisState (e j) := by
  have h := permutationUnitary_smul_col e j 1
  rw [one_smul] at h
  rw [basisState, Matrix.mulVec_single_one]
  exact h

/-- Bits of a `k`-bit index viewed inside `k + m` bits: the index bits, then zeros. -/
theorem basisBits_castLE (h : 2 ^ k ≤ 2 ^ (k + m)) (j : Fin (2 ^ k)) :
    basisBits (k + m) (Fin.castLE h j) = Fin.append (basisBits k j) (fun _ ↦ 0) := by
  funext i
  rw [basisBits_eq_div_mod]
  refine Fin.addCases (fun i' ↦ ?_) (fun i' ↦ ?_) i
  · rw [Fin.append_left, basisBits_eq_div_mod]
    rfl
  · rw [Fin.append_right]
    have hlt : j.val < 2 ^ (k + i'.val) :=
      lt_of_lt_of_le j.isLt (Nat.pow_le_pow_right (by decide) (Nat.le_add_right k i'.val))
    simp [Nat.div_eq_of_lt hlt]

/-- Bits read through a concatenated register. -/
theorem concat_bits (rT : QRegister k n) (rA : QRegister m n) (hdisj : rT.DisjointWires rA)
    (β : BitAssignment n) :
    (fun i ↦ β (rT.concat rA hdisj i)) =
      Fin.append (fun i ↦ β (rT i)) (fun i ↦ β (rA i)) := by
  funext i
  refine Fin.addCases (fun i' ↦ ?_) (fun i' ↦ ?_) i
  · rw [Fin.append_left, QRegister.concat_apply_left]
  · rw [Fin.append_right, QRegister.concat_apply_right]

theorem anc_bits_zero (rA : QRegister m n) (β : BitAssignment n) (hβ : localIdx rA β = 0)
    (i : Fin m) : β (rA i) = 0 := by
  have h := congrArg (basisBits m) hβ
  rw [localIdx, Equiv.apply_symm_apply, basisBits_zero] at h
  exact congrFun h i

/-- With zero ancillas, the combined index is the target index. -/
theorem localIdx_concat_of_anc_zero (rT : QRegister k n) (rA : QRegister m n)
    (hdisj : rT.DisjointWires rA) (h : 2 ^ k ≤ 2 ^ (k + m)) (β : BitAssignment n)
    (hβ : localIdx rA β = 0) :
    localIdx (rT.concat rA hdisj) β = Fin.castLE h (localIdx rT β) := by
  rw [localIdx, Equiv.symm_apply_eq, basisBits_castLE, concat_bits]
  congr 1
  · rw [localIdx, Equiv.apply_symm_apply]
  · funext i
    exact anc_bits_zero rA β hβ i

/-- With zero ancillas, writing target bits followed by zeros to the combined register is writing
the target bits to the target register. -/
theorem writeReg_concat_of_anc_zero (rT : QRegister k n) (rA : QRegister m n)
    (hdisj : rT.DisjointWires rA) (β : BitAssignment n) (hβ : localIdx rA β = 0)
    (γ : BitAssignment k) :
    writeReg β (rT.concat rA hdisj) (Fin.append γ (fun _ ↦ 0)) = writeReg β rT γ := by
  funext w
  by_cases hw : w ∈ Set.range (rT.concat rA hdisj).wires
  · obtain ⟨i, rfl⟩ := hw
    rw [writeReg_apply_reg]
    refine Fin.addCases (fun i' ↦ ?_) (fun i' ↦ ?_) i
    · rw [Fin.append_left, QRegister.concat_apply_left, writeReg_apply_reg]
    · rw [Fin.append_right, QRegister.concat_apply_right,
        writeReg_apply_of_not_mem _ _ _ _
          (fun hmem ↦ Set.disjoint_left.1 hdisj hmem ⟨i', rfl⟩),
        anc_bits_zero rA β hβ i']
  · have hT : w ∉ Set.range rT.wires := by
      rintro ⟨i, rfl⟩
      exact hw ⟨Fin.castAdd m i, QRegister.concat_apply_left rT rA hdisj i⟩
    rw [writeReg_apply_of_not_mem _ _ _ _ hw, writeReg_apply_of_not_mem _ _ _ _ hT]

/-- A set-of-outcomes projector acting on a basis ket. -/
theorem basisOutcomesProjector_mulVec_ket (r : QRegister k n) (S : Finset (Fin (2 ^ k)))
    (β : BitAssignment n) :
    (r.basisOutcomesProjector S).mulVec (ket β) = if localIdx r β ∈ S then ket β else 0 := by
  have hext : r.extractIndex ((basisBits n).symm β) = localIdx r β := by
    simp [QRegister.extractIndex]
  rw [ket, basisState, QRegister.basisOutcomesProjector, Matrix.diagonal_mulVec_single, hext]
  split_ifs <;> simp

variable [DecidableEq Var]

/-- An averaged Kraus lower bound `R` that maps every basis state with valid target data and zero
ancillas by the target permutation `σ` realizes `σ` as a clean subroutine on the encoding. -/
theorem realizesCleanSubroutineOnEncoding_of_lowerKraus [NeZero (2 ^ n)]
    (rTarget : QRegister k n) (rAnc : QRegister m n) (hdisj : rTarget.DisjointWires rAnc)
    (valid : Set (Fin (2 ^ k))) (σ : Equiv.Perm (Fin (2 ^ k)))
    {P : QProg Var (2 ^ n)} {R : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hP : LowerKraus P R)
    (hR : ∀ β, localIdx rAnc β = 0 → localIdx rTarget β ∈ valid →
      R.mulVec (ket β) = ket (writeReg β rTarget (basisBits k (σ (localIdx rTarget β))))) :
    RealizesCleanSubroutineOnEncoding rTarget rAnc hdisj valid σ P := by
  classical
  have hle : 2 ^ k ≤ 2 ^ (k + m) := Nat.pow_le_pow_right (by decide) (Nat.le_add_right k m)
  let τ : Equiv.Perm (Fin (2 ^ (k + m))) := σ.viaFintypeEmbedding (Fin.castLEEmb hle)
  have hτ : ∀ j, τ (Fin.castLE hle j) = Fin.castLE hle (σ j) := fun j ↦
    Equiv.Perm.viaFintypeEmbedding_apply_image σ (Fin.castLEEmb hle) j
  refine ⟨permutationUnitary τ, fun input _ ↦ ?_, ?_⟩
  · rw [permutationUnitary_mulVec_basisState]
    exact congrArg basisState (hτ input)
  · intro M s
    set E := (rTarget.concat rAnc hdisj).embedUnitary (permutationUnitary τ) with hEdef
    set S : Finset (Fin (2 ^ k)) := @Finset.filter _ valid
      (fun outcome ↦ Classical.propDecidable (outcome ∈ valid)) Finset.univ with hS
    have hE : ∀ β, localIdx rAnc β = 0 → E.1.mulVec (ket β) =
        ket (writeReg β rTarget (basisBits k (σ (localIdx rTarget β)))) := fun β hβ ↦ by
      have h := embedMatrix_permMatrix_mulVec_ket (rTarget.concat rAnc hdisj) τ⁻¹ β
      rw [Equiv.Perm.inv_def, Equiv.symm_symm] at h
      rw [hEdef, QRegister.embedUnitary_val]
      refine h.trans ?_
      rw [localIdx_concat_of_anc_zero rTarget rAnc hdisj hle β hβ, hτ, basisBits_castLE,
        writeReg_concat_of_anc_zero rTarget rAnc hdisj β hβ]
    have key : E.1 * rTarget.basisOutcomesProjector S * rAnc.basisOutcomeProjector 0 =
        R * rTarget.basisOutcomesProjector S * rAnc.basisOutcomeProjector 0 := by
      refine matrix_ext_ket fun β ↦ ?_
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, basisOutcomeProjector_mulVec_ket]
      by_cases hβ : localIdx rAnc β = 0
      · simp only [hβ, ↓reduceIte]
        rw [basisOutcomesProjector_mulVec_ket]
        by_cases hv : localIdx rTarget β ∈ S
        · simp only [hv, ↓reduceIte]
          rw [hE β hβ, hR β hβ
            ((@Finset.mem_filter _ (fun o ↦ o ∈ valid)
              (fun o ↦ Classical.propDecidable (o ∈ valid)) Finset.univ _).1 hv).2]
        · simp only [hv, ↓reduceIte, Matrix.mulVec_zero]
      · simp only [hβ, ↓reduceIte, Matrix.mulVec_zero]
    have key' : rAnc.basisOutcomeProjector 0 * (rTarget.basisOutcomesProjector S * (star E).1) =
        rAnc.basisOutcomeProjector 0 * (rTarget.basisOutcomesProjector S * Rᴴ) := by
      simpa [conjTranspose_mul, Matrix.mul_assoc, Matrix.star_eq_conjTranspose] using
        congrArg conjTranspose key
    change (((CQAssertion.qAssign E (fun _ ↦ M) s).1.conj (rTarget.basisOutcomesProjector S)).conj
        (rAnc.basisOutcomeProjector 0)) ≤
      (((wp P (fun _ ↦ M) s).1.conj (rTarget.basisOutcomesProjector S)).conj
        (rAnc.basisOutcomeProjector 0))
    have hpre : (CQAssertion.qAssign E (fun _ ↦ M) s).1 = M.1.conj (star E).1 := rfl
    rw [hpre]
    refine le_trans (le_of_eq ?_)
      (HermitianMat.conj_mono (HermitianMat.conj_mono (hP M s)))
    rw [HermitianMat.conj_conj, HermitianMat.conj_conj, HermitianMat.conj_conj,
      HermitianMat.conj_conj]
    simp only [Matrix.mul_assoc]
    rw [key']

end OnEncodingBridge

open Function WeierstrassCurve.Affine

/-- An injective map defined on the image of an injective encoding extends to a permutation. -/
theorem exists_perm_extending {ι α : Type*} [Fintype α] (enc out : ι → α)
    (henc : Injective enc) (hout : Injective out) :
    ∃ σ : Equiv.Perm α, ∀ a, σ (enc a) = out a := by
  classical
  let e : {x // x ∈ Set.range enc} ≃ {x // x ∈ Set.range out} :=
    (Equiv.ofInjective enc henc).symm.trans (Equiv.ofInjective out hout)
  refine ⟨e.extendSubtype, fun a ↦ ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e (enc a) ⟨a, rfl⟩]
  have h : (Equiv.ofInjective enc henc).symm ⟨enc a, ⟨a, rfl⟩⟩ = a :=
    Equiv.ofInjective_symm_apply henc a
  simp [e, h]

theorem pair_inj {A x y x' y' : ℕ} (hx : x < A) (hx' : x' < A)
    (h : x + A * y = x' + A * y') : x = x' ∧ y = y' := by
  have h1 : (x + A * y) % A = (x' + A * y') % A := by rw [h]
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hx'] at h1
  subst h1
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_left_cancel h)⟩

namespace FieldMulCore

open Function ArcsinImpl OnEncodingBridge

variable {n : ℕ}

/-- Little-endian bits of a natural number. -/
def natBits (k d : ℕ) : BitAssignment k := fun i ↦ ((d / 2 ^ (i : ℕ) % 2 : ℕ) : ZMod 2)

theorem basisBits_mk_eq_natBits (k m : ℕ) (hm : m < 2 ^ k) :
    basisBits k ⟨m, hm⟩ = natBits k m :=
  funext fun i ↦ basisBits_mk_apply m hm i

/-- All the disjointness facts the multiplier needs about its registers and single wires. -/
structure Wiring {w : ℕ} (rX rY : QRegister w n) (rB rA : QRegister (w + 1) n)
    (rC : QRegister w n) (ci f g : Wire n) : Prop where
  hAB : rA.DisjointWires rB
  hAC : rA.DisjointWires rC
  hBC : rB.DisjointWires rC
  hXY : rX.DisjointWires rY
  hXA : rX.DisjointWires rA
  hXB : rX.DisjointWires rB
  hXC : rX.DisjointWires rC
  hYA : rY.DisjointWires rA
  hYB : rY.DisjointWires rB
  hYC : rY.DisjointWires rC
  ciA : ci ∉ Set.range rA.wires
  ciB : ci ∉ Set.range rB.wires
  ciC : ci ∉ Set.range rC.wires
  ciX : ci ∉ Set.range rX.wires
  ciY : ci ∉ Set.range rY.wires
  fA : f ∉ Set.range rA.wires
  fB : f ∉ Set.range rB.wires
  fC : f ∉ Set.range rC.wires
  fX : f ∉ Set.range rX.wires
  fY : f ∉ Set.range rY.wires
  gA : g ∉ Set.range rA.wires
  gB : g ∉ Set.range rB.wires
  gC : g ∉ Set.range rC.wires
  gX : g ∉ Set.range rX.wires
  gY : g ∉ Set.range rY.wires
  cif : ci ≠ f
  cig : ci ≠ g
  fg : f ≠ g

/-- The adder workspace is clean: constant register, carries and carry-in are zero. -/
def Clean {w : ℕ} (rA : QRegister (w + 1) n) (rC : QRegister w n) (ci : Wire n)
    (β : BitAssignment n) : Prop :=
  (∀ i, β (rA i) = 0) ∧ (∀ i, β (rC i) = 0) ∧ β ci = 0

/-- `rB ← rB + c * d mod 2^(w+1)`: load the constant `d` into `rA` under the optional control `c`,
ripple-add, unload. -/
def caddcSteps (w : ℕ) (rB rA : QRegister (w + 1) n) (rC : QRegister w n) (ci : Wire n)
    (c : Option (Wire n)) (d : ℕ) : List (Step n) :=
  xorSteps c (w + 1) rA (natBits (w + 1) d) ++ rippleSteps w rA rB ci rC ++
    xorSteps c (w + 1) rA (natBits (w + 1) d)

theorem runList_caddc_lt {w : ℕ} {rX rY : QRegister w n} {rB rA : QRegister (w + 1) n}
    {rC : QRegister w n} {ci f g : Wire n} (hW : Wiring rX rY rB rA rC ci f g)
    (c : Option (Wire n)) (hcA : ∀ i, CtrlNe c (rA i)) (hcB : ∀ i, CtrlNe c (rB i))
    (hcC : ∀ i, CtrlNe c (rC i)) (hci : CtrlNe c ci)
    (d : ℕ) (hd : d < 2 ^ (w + 1)) (β : BitAssignment n) (hclean : Clean rA rC ci β)
    (v : ℕ) (hv : v < 2 ^ (w + 1)) :
    runList (caddcSteps w rB rA rC ci c d) (writeReg β rB (natBits (w + 1) v)) =
      some (writeReg β rB (natBits (w + 1) ((v + (ctrlVal c β).val * d) % 2 ^ (w + 1)))) := by
  have hAB := hW.hAB
  have hBA : rB.DisjointWires rA := QRegister.disjoint_comm.1 hAB
  obtain ⟨hA0, hC0, hci0⟩ := hclean
  have hnA : ∀ i, rA i ∉ Set.range rB.wires := fun i ↦ not_mem_of_disjoint hAB i
  have hnB : ∀ i, rB i ∉ Set.range rA.wires := fun i ↦ not_mem_of_disjoint hBA i
  have hnCA : ∀ i, rC i ∉ Set.range rA.wires := fun i ↦
    not_mem_of_disjoint (QRegister.disjoint_comm.1 hW.hAC) i
  have hnCB : ∀ i, rC i ∉ Set.range rB.wires := fun i ↦
    not_mem_of_disjoint (QRegister.disjoint_comm.1 hW.hBC) i
  obtain ⟨e, he⟩ : ∃ e, e = ctrlVal c β := ⟨_, rfl⟩
  rw [← he]
  have he1 : e.val ≤ 1 := by have := ZMod.val_lt e; omega
  have hlt : e.val * d < 2 ^ (w + 1) :=
    lt_of_le_of_lt (Nat.mul_le_mul_right d he1) (by omega)
  obtain ⟨S0, hS0⟩ : ∃ S0, S0 = writeReg β rB (natBits (w + 1) v) := ⟨_, rfl⟩
  rw [← hS0]
  have hS0A : ∀ i, S0 (rA i) = 0 := fun i ↦ by
    rw [hS0, writeReg_apply_of_not_mem _ _ _ _ (hnA i)]; exact hA0 i
  have hS0e : ctrlVal c S0 = e := by rw [hS0, ctrlVal_writeReg hcB, he]
  -- stage 1: load the constant
  obtain ⟨S1, hS1⟩ : ∃ S1, S1 = writeReg S0 rA (fun i ↦ e * natBits (w + 1) d i) := ⟨_, rfl⟩
  have h1 : runList (xorSteps c (w + 1) rA (natBits (w + 1) d)) S0 = some S1 := by
    have hf : (fun i ↦ S0 (rA i) + ctrlVal c S0 * natBits (w + 1) d i) =
        fun i ↦ e * natBits (w + 1) d i := funext fun i ↦ by rw [hS0A i, hS0e, zero_add]
    rw [runList_xorSteps c _ rA _ hcA, hf, hS1]
  have hγ : (fun i ↦ e * natBits (w + 1) d i) = natBits (w + 1) (e.val * d) := by
    funext i
    have h1v : (1 : ZMod 2).val = 1 := rfl
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) e with h | h
    · rw [h]; simp [natBits]
    · rw [h]; simp [natBits, h1v]
  have hidxA : (localIdx rA S1 : ℕ) = e.val * d := by
    rw [hS1, localIdx_writeReg, hγ, ← basisBits_mk_eq_natBits _ _ hlt]
    simp
  have hidxB : (localIdx rB S1 : ℕ) = v := by
    rw [hS1, localIdx_writeReg_of_disjoint _ _ _ hAB, hS0, localIdx_writeReg,
      ← basisBits_mk_eq_natBits _ _ hv]
    simp
  have hS1C : ∀ i, S1 (rC i) = 0 := fun i ↦ by
    rw [hS1, writeReg_apply_of_not_mem _ _ _ _ (hnCA i), hS0,
      writeReg_apply_of_not_mem _ _ _ _ (hnCB i)]
    exact hC0 i
  have hS1ci : S1 ci = 0 := by
    rw [hS1, writeReg_apply_of_not_mem _ _ _ _ hW.ciA, hS0,
      writeReg_apply_of_not_mem _ _ _ _ hW.ciB]
    exact hci0
  -- stage 2: ripple add
  obtain ⟨S2, hS2⟩ : ∃ S2, S2 = writeReg S1 rB
      (natBits (w + 1) ((v + e.val * d) % 2 ^ (w + 1))) := ⟨_, rfl⟩
  have h2 : runList (rippleSteps w rA rB ci rC) S1 = some S2 := by
    rw [runList_rippleSteps w rA rB ci rC hAB hW.hAC hW.hBC hW.ciA hW.ciB hW.ciC S1 hS1C,
      basisBits_mk_eq_natBits, hidxA, hidxB, hS1ci, ZMod.val_zero, hS2,
      show e.val * d + v + 0 = v + e.val * d by omega]
  -- stage 3: unload the constant
  have hS2A : ∀ i, S2 (rA i) = e * natBits (w + 1) d i := fun i ↦ by
    rw [hS2, writeReg_apply_of_not_mem _ _ _ _ (hnA i), hS1, writeReg_apply_reg]
  have hS2e : ctrlVal c S2 = e := by
    rw [hS2, ctrlVal_writeReg hcB, hS1, ctrlVal_writeReg hcA, hS0e]
  have h3 : runList (xorSteps c (w + 1) rA (natBits (w + 1) d)) S2 =
      some (writeReg S2 rA (fun _ ↦ 0)) := by
    have hf : (fun i ↦ S2 (rA i) + ctrlVal c S2 * natBits (w + 1) d i) = fun _ ↦ 0 :=
      funext fun i ↦ by rw [hS2A i, hS2e, CharTwo.add_self_eq_zero]
    rw [runList_xorSteps c _ rA _ hcA, hf]
  rw [caddcSteps, runList_append, runList_append, h1, Option.bind_some, h2, Option.bind_some, h3]
  congr 1
  funext x
  by_cases hxA : x ∈ Set.range rA.wires
  · obtain ⟨i, rfl⟩ := hxA
    rw [writeReg_apply_reg, writeReg_apply_of_not_mem _ _ _ _ (hnA i)]
    exact (hA0 i).symm
  · rw [writeReg_apply_of_not_mem _ _ _ _ hxA]
    by_cases hxB : x ∈ Set.range rB.wires
    · obtain ⟨i, rfl⟩ := hxB
      rw [hS2, writeReg_apply_reg, writeReg_apply_reg]
    · rw [hS2, writeReg_apply_of_not_mem _ _ _ _ hxB, writeReg_apply_of_not_mem _ _ _ _ hxB,
        hS1, writeReg_apply_of_not_mem _ _ _ _ hxA, hS0, writeReg_apply_of_not_mem _ _ _ _ hxB]

/-- Constants of any size: only `d mod 2^(w+1)` matters. -/
theorem runList_caddc {w : ℕ} {rX rY : QRegister w n} {rB rA : QRegister (w + 1) n}
    {rC : QRegister w n} {ci f g : Wire n} (hW : Wiring rX rY rB rA rC ci f g)
    (c : Option (Wire n)) (hcA : ∀ i, CtrlNe c (rA i)) (hcB : ∀ i, CtrlNe c (rB i))
    (hcC : ∀ i, CtrlNe c (rC i)) (hci : CtrlNe c ci)
    (d : ℕ) (β : BitAssignment n) (hclean : Clean rA rC ci β)
    (v : ℕ) (hv : v < 2 ^ (w + 1)) :
    runList (caddcSteps w rB rA rC ci c d) (writeReg β rB (natBits (w + 1) v)) =
      some (writeReg β rB (natBits (w + 1) ((v + (ctrlVal c β).val * d) % 2 ^ (w + 1)))) := by
  have hnat : natBits (w + 1) d = natBits (w + 1) (d % 2 ^ (w + 1)) := by
    funext i
    have hi : (i : ℕ) < w + 1 := i.isLt
    have hk : 2 ^ (w + 1) = 2 ^ (i : ℕ) * 2 ^ (w + 1 - (i : ℕ)) := by
      rw [← pow_add]; congr 1; omega
    simp only [natBits]
    rw [hk, Nat.mod_mul_right_div_self,
      Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega : w + 1 - (i : ℕ) ≠ 0))]
  have hdlt : d % 2 ^ (w + 1) < 2 ^ (w + 1) := Nat.mod_lt _ (by positivity)
  have hsteps : caddcSteps w rB rA rC ci c d = caddcSteps w rB rA rC ci c (d % 2 ^ (w + 1)) := by
    simp only [caddcSteps, hnat]
  have hm : (v + (ctrlVal c β).val * (d % 2 ^ (w + 1))) % 2 ^ (w + 1) =
      (v + (ctrlVal c β).val * d) % 2 ^ (w + 1) :=
    Nat.ModEq.add_left v ((Nat.mod_modEq d _).mul_left _)
  rw [hsteps, runList_caddc_lt hW c hcA hcB hcC hci _ hdlt β hclean v hv, hm]

theorem andCount_caddc (w : ℕ) (rB rA : QRegister (w + 1) n) (rC : QRegister w n) (ci : Wire n)
    (c : Option (Wire n)) (d : ℕ) :
    ((caddcSteps w rB rA rC ci c d).map Step.andCount).sum = w := by
  simp only [caddcSteps, List.map_append, List.sum_append, andCount_xorSteps,
    andCount_rippleSteps, zero_add, add_zero]

/-- The arithmetic of the controlled modular addition, with `A = 2^w` and `e` the control bit. -/
theorem mod_of_eq_lt {x y M : ℕ} (h : x = y) (hy : y < M) : x % M = y := by
  subst h; exact Nat.mod_eq_of_lt hy

theorem mod_of_eq_add_lt {x y M : ℕ} (h : x = y + M) (hy : y < M) : x % M = y := by
  subst h; rw [Nat.add_mod_right]; exact Nat.mod_eq_of_lt hy

theorem div_mod_two_zero {v A : ℕ} (h : v < A) : v / A % 2 = 0 := by
  rw [Nat.div_eq_of_lt h]

theorem div_mod_two_one {v A : ℕ} (h1 : A ≤ v) (h2 : v < 2 * A) : v / A % 2 = 1 := by
  rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]

/-- The arithmetic of the controlled modular addition, with `A = 2^w` and `e` the control bit, in
the form of the successive values `v1, ..., v5` of the accumulator and the flag bits `fb`, `hb`. -/
theorem modAdd_arith (A p t cst e v1 v2 fb v3 v4 hb v5 : ℕ) (hp : p < A) (ht : t < p)
    (hc : cst < p) (he : e ≤ 1)
    (h1 : v1 = (t + e * cst) % (2 * A))
    (h2 : v2 = (v1 + (2 * A - p)) % (2 * A))
    (hfb : fb = v2 / A % 2)
    (h3 : v3 = (v2 + fb * p) % (2 * A))
    (h4 : v4 = (v3 + e * (2 * A - cst)) % (2 * A))
    (hhb : hb = v4 / A % 2)
    (h5 : v5 = (v4 + e * cst) % (2 * A)) :
    v3 = (t + e * cst) % p ∧ (fb + hb + 1) % 2 = 0 ∧ v5 = (t + e * cst) % p := by
  rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
  · have e1 : v1 = t := h1.trans (mod_of_eq_lt (by omega) (by omega))
    have e2 : v2 = t + (2 * A - p) := h2.trans (mod_of_eq_lt (by omega) (by omega))
    have e3 : fb = 1 := hfb.trans (div_mod_two_one (by omega) (by omega))
    subst e3
    have e4 : v3 = t := h3.trans (mod_of_eq_add_lt (by omega) (by omega))
    have e5 : v4 = t := h4.trans (mod_of_eq_lt (by omega) (by omega))
    have e6 : hb = 0 := hhb.trans (div_mod_two_zero (by omega))
    have e7 : v5 = t := h5.trans (mod_of_eq_lt (by omega) (by omega))
    refine ⟨?_, ?_, ?_⟩
    · rw [e4, zero_mul, add_zero, Nat.mod_eq_of_lt ht]
    · omega
    · rw [e7, zero_mul, add_zero, Nat.mod_eq_of_lt ht]
  · by_cases hlt : t + cst < p
    · have e1 : v1 = t + cst := h1.trans (mod_of_eq_lt (by omega) (by omega))
      have e2 : v2 = t + cst + (2 * A - p) := h2.trans (mod_of_eq_lt (by omega) (by omega))
      have e3 : fb = 1 := hfb.trans (div_mod_two_one (by omega) (by omega))
      subst e3
      have e4 : v3 = t + cst := h3.trans (mod_of_eq_add_lt (by omega) (by omega))
      have e5 : v4 = t := h4.trans (mod_of_eq_add_lt (by omega) (by omega))
      have e6 : hb = 0 := hhb.trans (div_mod_two_zero (by omega))
      have e7 : v5 = t + cst := h5.trans (mod_of_eq_lt (by omega) (by omega))
      refine ⟨?_, ?_, ?_⟩
      · rw [e4, one_mul, Nat.mod_eq_of_lt hlt]
      · omega
      · rw [e7, one_mul, Nat.mod_eq_of_lt hlt]
    · have hm : (t + 1 * cst) % p = t + cst - p := by
        rw [one_mul, Nat.mod_eq_sub_mod (by omega)]
        exact Nat.mod_eq_of_lt (by omega)
      have e1 : v1 = t + cst := h1.trans (mod_of_eq_lt (by omega) (by omega))
      have e2 : v2 = t + cst - p := h2.trans (mod_of_eq_add_lt (by omega) (by omega))
      have e3 : fb = 0 := hfb.trans (div_mod_two_zero (by omega))
      subst e3
      have e4 : v3 = t + cst - p := h3.trans (mod_of_eq_lt (by omega) (by omega))
      have e5 : v4 = t + (2 * A - p) := h4.trans (mod_of_eq_lt (by omega) (by omega))
      have e6 : hb = 1 := hhb.trans (div_mod_two_one (by omega) (by omega))
      have e7 : v5 = t + cst - p := h5.trans (mod_of_eq_add_lt (by omega) (by omega))
      refine ⟨?_, ?_, ?_⟩
      · rw [e4, hm]
      · omega
      · rw [e7, hm]

/-- `rB ← rB + e * cst mod p` for `rB < p`, controlled on the wire `e`. The top wire of `rB` is the
overflow bit and `f` is the comparison flag; both end at zero. -/
def modAddSteps (w p : ℕ) (rB rA : QRegister (w + 1) n) (rC : QRegister w n) (ci f : Wire n)
    (e : Wire n) (cst : ℕ) : List (Step n) :=
  caddcSteps w rB rA rC ci (some e) cst ++
  caddcSteps w rB rA rC ci none (2 ^ (w + 1) - p) ++
  [Step.cnot (rB (Fin.last w)) f] ++
  caddcSteps w rB rA rC ci (some f) p ++
  caddcSteps w rB rA rC ci (some e) (2 ^ (w + 1) - cst) ++
  [Step.cnot (rB (Fin.last w)) f, Step.x f] ++
  caddcSteps w rB rA rC ci (some e) cst

theorem runList_modAdd {w p : ℕ} {rX rY : QRegister w n} {rB rA : QRegister (w + 1) n}
    {rC : QRegister w n} {ci f g : Wire n} (hW : Wiring rX rY rB rA rC ci f g)
    (e : Wire n) (heA : e ∉ Set.range rA.wires) (heB : e ∉ Set.range rB.wires)
    (heC : e ∉ Set.range rC.wires) (heci : e ≠ ci) (hef : e ≠ f)
    (cst : ℕ) (hcst : cst < p) (hp : p < 2 ^ w)
    (β : BitAssignment n) (hclean : Clean rA rC ci β) (hf : β f = 0)
    (v : ℕ) (hv : v < p) :
    runList (modAddSteps w p rB rA rC ci f e cst) (writeReg β rB (natBits (w + 1) v)) =
      some (writeReg β rB (natBits (w + 1) ((v + (β e).val * cst) % p))) := by
  have hefl : e ≠ f := hef
  have hAf : ∀ i, rA i ≠ f := fun i h ↦ hW.fA ⟨i, h⟩
  have hCf : ∀ i, rC i ≠ f := fun i h ↦ hW.fC ⟨i, h⟩
  have hcl : ∀ a : ZMod 2, Clean rA rC ci (update β f a) := fun a ↦
    ⟨fun i ↦ by rw [update_of_ne (hAf i)]; exact hclean.1 i,
     fun i ↦ by rw [update_of_ne (hCf i)]; exact hclean.2.1 i,
     by rw [update_of_ne hW.cif]; exact hclean.2.2⟩
  have K : ∀ (c : Option (Wire n)) (_ : ∀ i, CtrlNe c (rA i)) (_ : ∀ i, CtrlNe c (rB i))
      (_ : ∀ i, CtrlNe c (rC i)) (_ : CtrlNe c ci) (d : ℕ) (a : ZMod 2) (u : ℕ)
      (_ : u < 2 ^ (w + 1)),
      runList (caddcSteps w rB rA rC ci c d) (writeReg (update β f a) rB (natBits (w + 1) u)) =
        some (writeReg (update β f a) rB (natBits (w + 1)
          ((u + (ctrlVal c (update β f a)).val * d) % 2 ^ (w + 1)))) :=
    fun c hcA hcB hcC hci d a u hu ↦ runList_caddc hW c hcA hcB hcC hci d (update β f a) (hcl a) u hu
  -- the controls
  have cE : (∀ i, CtrlNe (some e) (rA i)) ∧ (∀ i, CtrlNe (some e) (rB i)) ∧
      (∀ i, CtrlNe (some e) (rC i)) ∧ CtrlNe (some e) ci :=
    ⟨fun i ↦ CtrlNe.some (fun h ↦ heA ⟨i, h.symm⟩), fun i ↦ CtrlNe.some (fun h ↦ heB ⟨i, h.symm⟩),
      fun i ↦ CtrlNe.some (fun h ↦ heC ⟨i, h.symm⟩), CtrlNe.some heci⟩
  have cF : (∀ i, CtrlNe (some f) (rA i)) ∧ (∀ i, CtrlNe (some f) (rB i)) ∧
      (∀ i, CtrlNe (some f) (rC i)) ∧ CtrlNe (some f) ci :=
    ⟨fun i ↦ CtrlNe.some (fun h ↦ hW.fA ⟨i, h.symm⟩), fun i ↦ CtrlNe.some (fun h ↦ hW.fB ⟨i, h.symm⟩),
      fun i ↦ CtrlNe.some (fun h ↦ hW.fC ⟨i, h.symm⟩), CtrlNe.some hW.cif.symm⟩
  have cN : (∀ i, CtrlNe none (rA i)) ∧ (∀ i, CtrlNe none (rB i)) ∧
      (∀ i, CtrlNe none (rC i)) ∧ CtrlNe none ci :=
    ⟨fun i ↦ ctrlNe_none _, fun i ↦ ctrlNe_none _, fun i ↦ ctrlNe_none _, ctrlNe_none _⟩
  have hcvE : ∀ a : ZMod 2, ctrlVal (some e) (update β f a) = β e := fun a ↦
    update_of_ne hefl _ _
  have hcvF : ∀ a : ZMod 2, ctrlVal (some f) (update β f a) = a := fun a ↦ update_self _ _ _
  have hcvN : ∀ a : ZMod 2, ctrlVal none (update β f a) = 1 := fun a ↦ rfl
  have h1v : (1 : ZMod 2).val = 1 := rfl
  -- flag helpers
  have hset : ∀ (a x : ZMod 2) (u : ℕ), update (writeReg (update β f a) rB (natBits (w + 1) u)) f x =
      writeReg (update β f x) rB (natBits (w + 1) u) := fun a x u ↦ by
    rw [← writeReg_update_of_not_mem _ _ _ hW.fB, update_idem]
  have hgetf : ∀ (a : ZMod 2) (γ : BitAssignment (w + 1)), writeReg (update β f a) rB γ f = a :=
    fun a γ ↦ by rw [writeReg_apply_of_not_mem _ _ _ _ hW.fB, update_self]
  have hne : rB (Fin.last w) ≠ f := fun h ↦ hW.fB ⟨Fin.last w, h⟩
  have hrunC : ∀ S : BitAssignment n, Step.run (Step.cnot (rB (Fin.last w)) f) S =
      some (update S f (S f + S (rB (Fin.last w)))) := fun S ↦ if_pos hne
  have hrunX : ∀ S : BitAssignment n, Step.run (Step.x f) S = some (update S f (S f + 1)) :=
    fun S ↦ rfl
  -- numbers
  obtain ⟨A, hA⟩ : ∃ A, A = 2 ^ w := ⟨_, rfl⟩
  have hA2 : 2 ^ (w + 1) = 2 * A := by rw [hA]; ring
  have hpA : p < A := by rw [hA]; exact hp
  have hbit : ∀ u : ℕ, natBits (w + 1) u (Fin.last w) = (((u / A % 2 : ℕ)) : ZMod 2) := fun u ↦ by
    simp only [natBits, Fin.val_last, hA]
  obtain ⟨eb, heb⟩ : ∃ eb, eb = (β e).val := ⟨_, rfl⟩
  have heb1 : eb ≤ 1 := by have := ZMod.val_lt (β e); omega
  rw [← heb]
  have hMpos : 0 < 2 ^ (w + 1) := by positivity
  have hlt : ∀ x : ℕ, x % 2 ^ (w + 1) < 2 ^ (w + 1) := fun x ↦ Nat.mod_lt _ hMpos
  obtain ⟨v1, hv1⟩ : ∃ v1, v1 = (v + eb * cst) % 2 ^ (w + 1) := ⟨_, rfl⟩
  obtain ⟨v2, hv2⟩ : ∃ v2, v2 = (v1 + 1 * (2 ^ (w + 1) - p)) % 2 ^ (w + 1) := ⟨_, rfl⟩
  obtain ⟨fb, hfb⟩ : ∃ fb, fb = v2 / A % 2 := ⟨_, rfl⟩
  obtain ⟨v3, hv3⟩ : ∃ v3, v3 = (v2 + fb * p) % 2 ^ (w + 1) := ⟨_, rfl⟩
  obtain ⟨v4, hv4⟩ : ∃ v4, v4 = (v3 + eb * (2 ^ (w + 1) - cst)) % 2 ^ (w + 1) := ⟨_, rfl⟩
  obtain ⟨hb, hhb⟩ : ∃ hb, hb = v4 / A % 2 := ⟨_, rfl⟩
  obtain ⟨v5, hv5⟩ : ∃ v5, v5 = (v4 + eb * cst) % 2 ^ (w + 1) := ⟨_, rfl⟩
  have hv1lt : v1 < 2 ^ (w + 1) := by rw [hv1]; exact hlt _
  have hv2lt : v2 < 2 ^ (w + 1) := by rw [hv2]; exact hlt _
  have hv3lt : v3 < 2 ^ (w + 1) := by rw [hv3]; exact hlt _
  have hv4lt : v4 < 2 ^ (w + 1) := by rw [hv4]; exact hlt _
  have hvlt : v < 2 ^ (w + 1) := by omega
  have harith := modAdd_arith A p v cst eb v1 v2 fb v3 v4 hb v5 hpA hv hcst heb1
    (by rw [hv1, hA2]) (by rw [hv2, hA2, one_mul]) hfb (by rw [hv3, hA2])
    (by rw [hv4, hA2]) hhb (by rw [hv5, hA2])
  have hfbval : ((fb : ℕ) : ZMod 2).val = fb := by
    rw [ZMod.val_natCast, hfb, Nat.mod_mod]
  have hflag0 : ((fb : ℕ) : ZMod 2) + natBits (w + 1) v4 (Fin.last w) + 1 = 0 := by
    have h0 : (((fb + hb + 1 : ℕ)) : ZMod 2) = 0 := by
      rw [← ZMod.natCast_mod (fb + hb + 1) 2, harith.2.1, Nat.cast_zero]
    push_cast at h0
    rw [hbit, ← hhb]
    exact h0
  have hupd0 : update β f 0 = β := by
    funext x
    by_cases h : x = f
    · rw [h, update_self, hf]
    · rw [update_of_ne h]
  -- the seven stages
  have s1 : runList (caddcSteps w rB rA rC ci (some e) cst)
      (writeReg (update β f 0) rB (natBits (w + 1) v)) =
      some (writeReg (update β f 0) rB (natBits (w + 1) v1)) := by
    rw [K _ cE.1 cE.2.1 cE.2.2.1 cE.2.2.2 cst 0 v hvlt, hcvE, ← heb, hv1]
  have s2 : runList (caddcSteps w rB rA rC ci none (2 ^ (w + 1) - p))
      (writeReg (update β f 0) rB (natBits (w + 1) v1)) =
      some (writeReg (update β f 0) rB (natBits (w + 1) v2)) := by
    rw [K _ cN.1 cN.2.1 cN.2.2.1 cN.2.2.2 _ 0 v1 hv1lt, hcvN, h1v, hv2]
  have s3 : runList [Step.cnot (rB (Fin.last w)) f]
      (writeReg (update β f 0) rB (natBits (w + 1) v2)) =
      some (writeReg (update β f ((fb : ℕ) : ZMod 2)) rB (natBits (w + 1) v2)) := by
    rw [runList_cons, hrunC, Option.bind_some, runList_nil, hgetf, writeReg_apply_reg, hset,
      zero_add, hbit, hfb]
  have s4 : runList (caddcSteps w rB rA rC ci (some f) p)
      (writeReg (update β f ((fb : ℕ) : ZMod 2)) rB (natBits (w + 1) v2)) =
      some (writeReg (update β f ((fb : ℕ) : ZMod 2)) rB (natBits (w + 1) v3)) := by
    rw [K _ cF.1 cF.2.1 cF.2.2.1 cF.2.2.2 p _ v2 hv2lt, hcvF, hfbval, hv3]
  have s5 : runList (caddcSteps w rB rA rC ci (some e) (2 ^ (w + 1) - cst))
      (writeReg (update β f ((fb : ℕ) : ZMod 2)) rB (natBits (w + 1) v3)) =
      some (writeReg (update β f ((fb : ℕ) : ZMod 2)) rB (natBits (w + 1) v4)) := by
    rw [K _ cE.1 cE.2.1 cE.2.2.1 cE.2.2.2 _ _ v3 hv3lt, hcvE, ← heb, hv4]
  have s6 : runList [Step.cnot (rB (Fin.last w)) f, Step.x f]
      (writeReg (update β f ((fb : ℕ) : ZMod 2)) rB (natBits (w + 1) v4)) =
      some (writeReg (update β f 0) rB (natBits (w + 1) v4)) := by
    rw [runList_cons, hrunC, Option.bind_some, runList_cons, hrunX, Option.bind_some,
      runList_nil, update_self, update_idem, hgetf, writeReg_apply_reg, hset, hflag0]
  have s7 : runList (caddcSteps w rB rA rC ci (some e) cst)
      (writeReg (update β f 0) rB (natBits (w + 1) v4)) =
      some (writeReg (update β f 0) rB (natBits (w + 1) v5)) := by
    rw [K _ cE.1 cE.2.1 cE.2.2.1 cE.2.2.2 cst 0 v4 hv4lt, hcvE, ← heb, hv5]
  have hinit : writeReg β rB (natBits (w + 1) v) =
      writeReg (update β f 0) rB (natBits (w + 1) v) := by rw [hupd0]
  rw [hinit, modAddSteps, runList_append, runList_append, runList_append, runList_append,
    runList_append, runList_append, s1, Option.bind_some, s2, Option.bind_some, s3,
    Option.bind_some, s4, Option.bind_some, s5, Option.bind_some, s6, Option.bind_some, s7,
    hupd0, harith.2.2]

theorem andCount_modAdd (w p : ℕ) (rB rA : QRegister (w + 1) n) (rC : QRegister w n)
    (ci f e : Wire n) (cst : ℕ) :
    ((modAddSteps w p rB rA rC ci f e cst).map Step.andCount).sum = 5 * w := by
  simp only [modAddSteps, List.map_append, List.sum_append, andCount_caddc, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Step.andCount]
  omega

/-- One partial product: `rB ← rB + x_i y_j (2^(i+j) mod p) mod p`. -/
def pairSteps (w p : ℕ) (rX rY : QRegister w n) (rB rA : QRegister (w + 1) n)
    (rC : QRegister w n) (ci f g : Wire n) (i j : Fin w) : List (Step n) :=
  [Step.and4t (rX i) (rY j) g] ++
  modAddSteps w p rB rA rC ci f g (2 ^ (i.val + j.val) % p) ++
  [Step.unand (rX i) (rY j) g]

theorem runList_pair {w p : ℕ} {rX rY : QRegister w n} {rB rA : QRegister (w + 1) n}
    {rC : QRegister w n} {ci f g : Wire n} (hW : Wiring rX rY rB rA rC ci f g)
    (hp0 : 0 < p) (hp : p < 2 ^ w)
    (β : BitAssignment n) (hclean : Clean rA rC ci β) (hf : β f = 0) (hg : β g = 0)
    (v : ℕ) (hv : v < p) (i j : Fin w) :
    runList (pairSteps w p rX rY rB rA rC ci f g i j) (writeReg β rB (natBits (w + 1) v)) =
      some (writeReg β rB (natBits (w + 1)
        ((v + (β (rX i)).val * (β (rY j)).val * (2 ^ (i.val + j.val) % p)) % p))) := by
  have hxy : rX i ≠ rY j := fun h ↦ not_mem_of_disjoint hW.hXY i ⟨j, h.symm⟩
  have hxg : rX i ≠ g := fun h ↦ hW.gX ⟨i, h⟩
  have hyg : rY j ≠ g := fun h ↦ hW.gY ⟨j, h⟩
  have hxB : rX i ∉ Set.range rB.wires := not_mem_of_disjoint hW.hXB i
  have hyB : rY j ∉ Set.range rB.wires := not_mem_of_disjoint hW.hYB j
  have hcond : rX i ≠ rY j ∧ rX i ≠ g ∧ rY j ≠ g := ⟨hxy, hxg, hyg⟩
  have hmulval : ∀ a b : ZMod 2, (a * b).val = a.val * b.val := by decide
  obtain ⟨x, hx⟩ : ∃ x, x = β (rX i) * β (rY j) := ⟨_, rfl⟩
  have hxval : x.val = (β (rX i)).val * (β (rY j)).val := by rw [hx, hmulval]
  have hclean' : Clean rA rC ci (update β g x) :=
    ⟨fun k ↦ by rw [update_of_ne (fun h ↦ hW.gA ⟨k, h⟩)]; exact hclean.1 k,
     fun k ↦ by rw [update_of_ne (fun h ↦ hW.gC ⟨k, h⟩)]; exact hclean.2.1 k,
     by rw [update_of_ne hW.cig]; exact hclean.2.2⟩
  have hf' : update β g x f = 0 := by rw [update_of_ne hW.fg]; exact hf
  have hupd0 : update β g 0 = β := by
    funext y
    by_cases h : y = g
    · rw [h, update_self, hg]
    · rw [update_of_ne h]
  have r1 : ∀ γ : BitAssignment (w + 1), runList [Step.and4t (rX i) (rY j) g] (writeReg β rB γ) =
      some (writeReg (update β g x) rB γ) := fun γ ↦ by
    have hS0g : writeReg β rB γ g = 0 := by
      rw [writeReg_apply_of_not_mem _ _ _ _ hW.gB]; exact hg
    have hr : Step.run (Step.and4t (rX i) (rY j) g) (writeReg β rB γ) =
        some (update (writeReg β rB γ) g (writeReg β rB γ (rX i) * writeReg β rB γ (rY j))) := by
      simp only [Step.run, ite_eq_left hcond, ite_eq_left hS0g]
    rw [runList_cons, hr, Option.bind_some, runList_nil, writeReg_apply_of_not_mem _ _ _ _ hxB,
      writeReg_apply_of_not_mem _ _ _ _ hyB, ← hx, writeReg_update_of_not_mem _ _ _ hW.gB]
  have r2 := runList_modAdd hW g hW.gA hW.gB hW.gC hW.cig.symm hW.fg.symm
    (2 ^ (i.val + j.val) % p) (Nat.mod_lt _ hp0) hp (update β g x) hclean' hf' v hv
  rw [update_self, hxval] at r2
  have r3 : ∀ γ : BitAssignment (w + 1), runList [Step.unand (rX i) (rY j) g]
      (writeReg (update β g x) rB γ) = some (writeReg β rB γ) := fun γ ↦ by
    have h0g : writeReg (update β g x) rB γ g = x := by
      rw [writeReg_apply_of_not_mem _ _ _ _ hW.gB, update_self]
    have h0x : writeReg (update β g x) rB γ (rX i) = β (rX i) := by
      rw [writeReg_apply_of_not_mem _ _ _ _ hxB, update_of_ne hxg]
    have h0y : writeReg (update β g x) rB γ (rY j) = β (rY j) := by
      rw [writeReg_apply_of_not_mem _ _ _ _ hyB, update_of_ne hyg]
    have hc : writeReg (update β g x) rB γ g =
        writeReg (update β g x) rB γ (rX i) * writeReg (update β g x) rB γ (rY j) := by
      rw [h0g, h0x, h0y, hx]
    have hr : Step.run (Step.unand (rX i) (rY j) g) (writeReg (update β g x) rB γ) =
        some (update (writeReg (update β g x) rB γ) g 0) := by
      simp only [Step.run, ite_eq_left hcond, ite_eq_left hc]
    rw [runList_cons, hr, Option.bind_some, runList_nil,
      ← writeReg_update_of_not_mem _ _ _ hW.gB, update_idem, hupd0]
  rw [pairSteps, runList_append, runList_append, r1, Option.bind_some, r2, Option.bind_some, r3]

/-- The multiplier: all `w * w` partial products. -/
def mulSteps (w p : ℕ) (rX rY : QRegister w n) (rB rA : QRegister (w + 1) n)
    (rC : QRegister w n) (ci f g : Wire n) : List (Step n) :=
  (List.finRange w).flatMap fun i ↦ (List.finRange w).flatMap fun j ↦
    pairSteps w p rX rY rB rA rC ci f g i j

theorem runList_mul {w p : ℕ} {rX rY : QRegister w n} {rB rA : QRegister (w + 1) n}
    {rC : QRegister w n} {ci f g : Wire n} (hW : Wiring rX rY rB rA rC ci f g)
    (hp0 : 0 < p) (hp : p < 2 ^ w)
    (β : BitAssignment n) (hclean : Clean rA rC ci β) (hf : β f = 0) (hg : β g = 0)
    (v : ℕ) (hv : v < p) :
    runList (mulSteps w p rX rY rB rA rC ci f g) (writeReg β rB (natBits (w + 1) v)) =
      some (writeReg β rB (natBits (w + 1)
        ((v + (localIdx rX β : ℕ) * (localIdx rY β : ℕ)) % p))) := by
  have hflat : ∀ {α : Type} (L : List α) (F : α → List (Step n)) (t : α → ℕ),
      (∀ a, ∀ u, u < p → runList (F a) (writeReg β rB (natBits (w + 1) u)) =
        some (writeReg β rB (natBits (w + 1) ((u + t a) % p)))) →
      ∀ u, u < p → runList (L.flatMap F) (writeReg β rB (natBits (w + 1) u)) =
        some (writeReg β rB (natBits (w + 1) ((u + (L.map t).sum) % p))) := by
    intro α L F t hF
    induction L with
    | nil =>
      intro u hu
      simp only [List.flatMap_nil, List.map_nil, List.sum_nil, add_zero, Nat.mod_eq_of_lt hu,
        runList_nil]
    | cons a L ih =>
      intro u hu
      rw [List.flatMap_cons, runList_append, hF a u hu, Option.bind_some,
        ih _ (Nat.mod_lt _ hp0), List.map_cons, List.sum_cons, Nat.mod_add_mod, add_assoc]
  have hin : ∀ i : Fin w, ∀ u, u < p →
      runList ((List.finRange w).flatMap fun j ↦ pairSteps w p rX rY rB rA rC ci f g i j)
        (writeReg β rB (natBits (w + 1) u)) =
      some (writeReg β rB (natBits (w + 1) ((u + ((List.finRange w).map fun j ↦
        (β (rX i)).val * (β (rY j)).val * (2 ^ (i.val + j.val) % p)).sum) % p))) :=
    fun i ↦ hflat (List.finRange w) (fun j ↦ pairSteps w p rX rY rB rA rC ci f g i j)
      (fun j ↦ (β (rX i)).val * (β (rY j)).val * (2 ^ (i.val + j.val) % p))
      (fun j u hu ↦ runList_pair hW hp0 hp β hclean hf hg u hu i j)
  have hout := hflat (List.finRange w)
    (fun i ↦ (List.finRange w).flatMap fun j ↦ pairSteps w p rX rY rB rA rC ci f g i j)
    (fun i ↦ ((List.finRange w).map fun j ↦
      (β (rX i)).val * (β (rY j)).val * (2 ^ (i.val + j.val) % p)).sum)
    (fun i u hu ↦ hin i u hu) v hv
  unfold mulSteps
  rw [hout]
  refine congrArg some (congrArg (writeReg β rB) (congrArg (natBits (w + 1)) ?_))
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).1
  rw [localIdx_val rX, localIdx_val rY]
  simp only [← Fin.sum_univ_def, Nat.cast_add, Nat.cast_sum, Nat.cast_mul, ZMod.natCast_mod,
    Nat.cast_pow, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [pow_add]
  ring

theorem andCount_mul (w p : ℕ) (rX rY : QRegister w n) (rB rA : QRegister (w + 1) n)
    (rC : QRegister w n) (ci f g : Wire n) :
    ((mulSteps w p rX rY rB rA rC ci f g).map Step.andCount).sum = w * w * (5 * w + 1) := by
  have hpair : ∀ i j, ((pairSteps w p rX rY rB rA rC ci f g i j).map Step.andCount).sum =
      5 * w + 1 := fun i j ↦ by
    simp only [pairSteps, List.map_append, List.sum_append, andCount_modAdd, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Step.andCount]
    omega
  have hflat : ∀ {α : Type} (L : List α) (F : α → List (Step n)) (c : ℕ),
      (∀ a, ((F a).map Step.andCount).sum = c) →
      (((L.flatMap F).map Step.andCount).sum = L.length * c) := by
    intro α L F c hF
    induction L with
    | nil => simp
    | cons a L ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, hF, ih, List.length_cons]
      ring
  unfold mulSteps
  rw [hflat (List.finRange w) _ (w * (5 * w + 1)), List.length_finRange, ← mul_assoc]
  intro i
  rw [hflat (List.finRange w) _ (5 * w + 1) (hpair i), List.length_finRange]

end FieldMulCore

/-!
## Curve, Encoding & Valid Inputs
-/

/-- The short Weierstrass curve `y² = x³ + a x + b` over `ZMod p`, in affine coordinates. -/
abbrev ecProjCurve {p : ℕ} (a b : ZMod p) : WeierstrassCurve.Affine (ZMod p) :=
  ⟨0, 0, 0, a, b⟩

/-- A projective triple over `ZMod p`: `(X, Y, Z)`. -/
abbrev ProjTriple (p : ℕ) : Type := ZMod p × ZMod p × ZMod p

/-- The triple `T = (X, Y, Z)` represents the affine point `(x, y)`: `Z ≠ 0`, `X = x * Z` and
`Y = y * Z`. -/
def IsProjRep {p : ℕ} (T : ProjTriple p) (x y : ZMod p) : Prop :=
  T.2.2 ≠ 0 ∧ T.1 = x * T.2.2 ∧ T.2.1 = y * T.2.2

/-- Index `(X + 2^w * Y + 2^(2w) * Z) mod 2^(3w)` of the `3 * w` wires holding a triple. The
reduction only makes the definition total: it does nothing when `p ≤ 2^w`. -/
def ecProjEncode (w : ℕ) {p : ℕ} (T : ProjTriple p) : Fin (2 ^ (3 * w)) :=
  ⟨(T.1.val + 2 ^ w * T.2.1.val + 2 ^ (2 * w) * T.2.2.val) % 2 ^ (3 * w),
    Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- Index of the `2 * (3 * w)`-qubit data register holding the input triple `T` in its first
`3 * w` wires and the output triple `R` in its last `3 * w` wires. -/
def ecProjPairEncode (w : ℕ) {p : ℕ} (T R : ProjTriple p) : Fin (2 ^ (2 * (3 * w))) :=
  ⟨((ecProjEncode w T).val + 2 ^ (3 * w) * (ecProjEncode w R).val) % 2 ^ (2 * (3 * w)),
    Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- Valid inputs: the input triple represents a nonsingular affine point `(x, y)` of
`ecProjCurve a b` with `x ≠ xQ`, and the output triple is zero. -/
def ecAddProjValidInputs (w : ℕ) {p : ℕ} (a b xQ : ZMod p) : Set (Fin (2 ^ (2 * (3 * w)))) :=
  {u | ∃ (x y : ZMod p) (T : ProjTriple p), (ecProjCurve a b).Nonsingular x y ∧ x ≠ xQ ∧
    IsProjRep T x y ∧ u = ecProjPairEncode w T (0, 0, 0)}

/-- The table `f` computes addition of the classical point `Q = (xQ, yQ)`: whenever `T` represents
an affine point `(x, y)` with `x ≠ xQ` and `(x, y) + Q = (x', y')` in the Mathlib group law,
`f T` represents `(x', y')`. -/
def IsECAddProjTable {p : ℕ} [Fact p.Prime] (a b xQ yQ : ZMod p)
    (hQ : (ecProjCurve a b).Nonsingular xQ yQ) (f : ProjTriple p → ProjTriple p) : Prop :=
  ∀ (x y : ZMod p) (h : (ecProjCurve a b).Nonsingular x y), x ≠ xQ →
    ∀ T : ProjTriple p, IsProjRep T x y →
      ∀ (x' y' : ZMod p) (h' : (ecProjCurve a b).Nonsingular x' y'),
        Point.some x y h + Point.some xQ yQ hQ = Point.some x' y' h' →
          IsProjRep (f T) x' y'

/-- The basis permutation `σ` writes the table `f` into a zeroed output register on valid inputs:
it maps the encoding of `(T, 0)` to the encoding of `(T, f T)`. -/
def IsECAddProjPerm (w : ℕ) {p : ℕ} (a b xQ : ZMod p) (f : ProjTriple p → ProjTriple p)
    (σ : Equiv.Perm (Fin (2 ^ (2 * (3 * w))))) : Prop :=
  ∀ (x y : ZMod p), (ecProjCurve a b).Nonsingular x y → x ≠ xQ →
    ∀ T : ProjTriple p, IsProjRep T x y →
      σ (ecProjPairEncode w T (0, 0, 0)) = ecProjPairEncode w T (f T)

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive ECPointAddProj.Var where | v deriving DecidableEq, Inhabited

open ECPointAddProj (Var)
open ECPointAddProj.Var (v)


theorem ecProjEncode_injective (w p : ℕ) [NeZero p] (hhi : p ≤ 2 ^ w) :
    Injective (ecProjEncode w (p := p)) := by
  have h2 : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by rw [two_mul, pow_add]
  have h3 : 2 ^ (3 * w) = 2 ^ w * 2 ^ w * 2 ^ w := by
    rw [show 3 * w = w + w + w by omega, pow_add, pow_add]
  have hlt : ∀ z : ZMod p, z.val < 2 ^ w := fun z ↦ lt_of_lt_of_le (ZMod.val_lt z) hhi
  have hb : ∀ x y t : ZMod p, x.val + 2 ^ w * y.val + 2 ^ (2 * w) * t.val < 2 ^ (3 * w) := by
    intro x y t
    have hx := hlt x
    have h1 : 2 ^ w * (y.val + 1) ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul_left _ (hlt y)
    have h4 : 2 ^ w * 2 ^ w * (t.val + 1) ≤ 2 ^ w * 2 ^ w * 2 ^ w := Nat.mul_le_mul_left _ (hlt t)
    rw [h2, h3]
    rw [mul_add, mul_one] at h1 h4
    linarith
  rintro ⟨x, y, t⟩ ⟨x', y', t'⟩ h
  have hv := congrArg Fin.val h
  simp only [ecProjEncode] at hv
  rw [Nat.mod_eq_of_lt (hb x y t), Nat.mod_eq_of_lt (hb x' y' t'), h2] at hv
  have hv' : x.val + 2 ^ w * (y.val + 2 ^ w * t.val) = x'.val + 2 ^ w * (y'.val + 2 ^ w * t'.val) := by
    linarith
  obtain ⟨e1, e2⟩ := pair_inj (hlt x) (hlt x') hv'
  obtain ⟨e3, e4⟩ := pair_inj (hlt y) (hlt y') e2
  rw [ZMod.val_injective p e1, ZMod.val_injective p e3, ZMod.val_injective p e4]

theorem ecProjPairEncode_injective (w p : ℕ) [NeZero p] (hhi : p ≤ 2 ^ w) :
    Injective fun TR : ProjTriple p × ProjTriple p ↦ ecProjPairEncode w TR.1 TR.2 := by
  have hpow : 2 ^ (2 * (3 * w)) = 2 ^ (3 * w) * 2 ^ (3 * w) := by rw [two_mul, pow_add]
  have hb : ∀ u v : Fin (2 ^ (3 * w)), u.val + 2 ^ (3 * w) * v.val < 2 ^ (2 * (3 * w)) := by
    intro u v
    have hu := u.isLt
    have h1 : 2 ^ (3 * w) * (v.val + 1) ≤ 2 ^ (3 * w) * 2 ^ (3 * w) :=
      Nat.mul_le_mul_left _ v.isLt
    rw [hpow]
    rw [mul_add, mul_one] at h1
    linarith
  rintro ⟨T, R⟩ ⟨T', R'⟩ h
  have hv := congrArg Fin.val h
  simp only [ecProjPairEncode] at hv
  rw [Nat.mod_eq_of_lt (hb _ _), Nat.mod_eq_of_lt (hb _ _)] at hv
  obtain ⟨e1, e2⟩ := pair_inj (Fin.isLt _) (Fin.isLt _) hv
  rw [ecProjEncode_injective w p hhi (Fin.ext e1), ecProjEncode_injective w p hhi (Fin.ext e2)]

/-- For every table, a permutation writing it into a zeroed output register exists. -/
theorem exists_isECAddProjPerm (w p : ℕ) [NeZero p] (hhi : p ≤ 2 ^ w) (a b xQ : ZMod p)
    (f : ProjTriple p → ProjTriple p) :
    ∃ σ, IsECAddProjPerm w a b xQ f σ := by
  have henc := ecProjPairEncode_injective w p hhi
  obtain ⟨σ, hσ⟩ := exists_perm_extending
    (fun T : ProjTriple p ↦ ecProjPairEncode w T (0, 0, 0))
    (fun T : ProjTriple p ↦ ecProjPairEncode w T (f T))
    (fun T T' e ↦ congrArg Prod.fst (henc (a₁ := (T, (0, 0, 0))) (a₂ := (T', (0, 0, 0))) e))
    (fun T T' e ↦ congrArg Prod.fst (henc (a₁ := (T, f T)) (a₂ := (T', f T')) e))
  exact ⟨σ, fun x y _ _ T _ ↦ hσ T⟩

/-!
## Stage A: the inversion-free table
-/

/-- Projective mixed addition of `T = (X, Y, Z)` and the affine point `Q = (xQ, yQ)`:
`u = yQ Z - Y`, `s = xQ Z - X`, `A = u² Z - s³ - 2 s² X`, and the result is
`(s A, u (s² X - A) - s³ Y, s³ Z)`. -/
def projAddFn {p : ℕ} (xQ yQ : ZMod p) (T : ProjTriple p) : ProjTriple p :=
  let uu := yQ * T.2.2 - T.2.1
  let ss := xQ * T.2.2 - T.1
  let AA := uu ^ 2 * T.2.2 - ss ^ 3 - 2 * ss ^ 2 * T.1
  (ss * AA, uu * (ss ^ 2 * T.1 - AA) - ss ^ 3 * T.2.1, ss ^ 3 * T.2.2)

theorem projAddFn_table {p : ℕ} [Fact p.Prime] (a b xQ yQ : ZMod p)
    (hQ : (ecProjCurve a b).Nonsingular xQ yQ) :
    IsECAddProjTable a b xQ yQ hQ (projAddFn xQ yQ) := by
  intro x y h hx T hT x' y' h' hadd
  obtain ⟨hZ, hX, hY⟩ := hT
  rw [Point.add_of_X_ne hx] at hadd
  simp only [Point.some.injEq] at hadd
  obtain ⟨e1, e2⟩ := hadd
  have hne : xQ - x ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hsl : (ecProjCurve a b).slope x xQ y yQ = (y - yQ) / (x - xQ) :=
    slope_of_X_ne hx
  have hs : xQ * T.2.2 - T.1 ≠ 0 := by
    rw [hX, ← sub_mul]; exact mul_ne_zero hne hZ
  have hxne : x - xQ ≠ 0 := sub_ne_zero.2 hx
  refine ⟨?_, ?_, ?_⟩
  · simp only [projAddFn]
    exact mul_ne_zero (pow_ne_zero 3 hs) hZ
  · rw [← e1, hsl]
    simp only [projAddFn, WeierstrassCurve.Affine.addX]
    rw [hX, hY]
    field_simp
    ring
  · rw [← e2, hsl]
    simp only [projAddFn, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX]
    rw [hX, hY]
    field_simp
    ring

/-!
## Stage B: copy steps and tameness
-/

namespace ProjPoly

open ArcsinImpl OnEncodingBridge FieldMulCore

variable {n : ℕ}

/-- CNOT copy of `s` onto `d`: `d ← d ⊕ s`. -/
def copySteps : (k : ℕ) → QRegister k n → QRegister k n → List (Step n)
  | 0, _, _ => []
  | k + 1, s, d => Step.cnot (s 0) (d 0) :: copySteps k (regTail s) (regTail d)

theorem runList_copySteps : ∀ (k : ℕ) (s d : QRegister k n), s.DisjointWires d →
    ∀ β : BitAssignment n,
    runList (copySteps k s d) β = some (writeReg β d (fun i ↦ β (d i) + β (s i))) := by
  intro k
  induction k with
  | zero =>
    intro s d _ β
    rw [copySteps, runList_nil,
      show (fun i : Fin 0 ↦ β (d i) + β (s i)) = fun i ↦ β (d i) from funext fun i ↦ i.elim0,
      writeReg_self]
  | succ k ih =>
    intro s d hsd β
    have hne : s 0 ≠ d 0 := hsd.ne 0 0
    have hsd' : (regTail s).DisjointWires (regTail d) :=
      QRegister.disjoint_iff.2 fun i j ↦ by
        rw [regTail_apply, regTail_apply]; exact hsd.ne _ _
    have hs : ∀ i : Fin k, s i.succ ≠ d 0 := fun i ↦ hsd.ne _ _
    have hd : ∀ i : Fin k, d i.succ ≠ d 0 := fun i h ↦ Fin.succ_ne_zero i (d.wires.injective h)
    have hrun : Step.run (Step.cnot (s 0) (d 0)) β =
        some (update β (d 0) (β (d 0) + β (s 0))) := ite_eq_left hne
    rw [copySteps, runList_cons, hrun, Option.bind_some, ih (regTail s) (regTail d) hsd',
      writeReg_succ β d, writeReg_update_of_not_mem _ _ _ (zero_not_mem_regTail d)]
    congr 3
    funext i
    rw [regTail_apply, regTail_apply, update_of_ne (hs i), update_of_ne (hd i)]

theorem andCount_copySteps : ∀ (k : ℕ) (s d : QRegister k n),
    ((copySteps k s d).map Step.andCount).sum = 0 := by
  intro k
  induction k with
  | zero => intro s d; rfl
  | succ k ih =>
    intro s d
    rw [copySteps, List.map_cons, List.sum_cons, ih]
    rfl

/-- A step with an exact inverse, all of whose wires satisfy `P`. -/
def Tame (P : Wire n → Prop) : Step n → Prop
  | Step.x q => P q
  | Step.cnot c t => P c ∧ P t
  | Step.and4t a b t => P a ∧ P b ∧ P t
  | Step.unand a b t => P a ∧ P b ∧ P t
  | _ => False

theorem Tame.noUnxor {P : Wire n → Prop} {s : Step n} (h : Tame P s) : s.NoUnxor := by
  cases s <;> first | exact trivial | exact h.elim

theorem Tame.avoids {P : Wire n → Prop} {s : Step n} (h : Tame P s) {w : Wire n}
    (hw : ¬ P w) : s.Avoids w := by
  cases s with
  | x q => exact fun e ↦ hw (e ▸ h)
  | cnot c t => exact ⟨fun e ↦ hw (e ▸ h.1), fun e ↦ hw (e ▸ h.2)⟩
  | and4t a b t => exact ⟨fun e ↦ hw (e ▸ h.1), fun e ↦ hw (e ▸ h.2.1), fun e ↦ hw (e ▸ h.2.2)⟩
  | unand a b t => exact ⟨fun e ↦ hw (e ▸ h.1), fun e ↦ hw (e ▸ h.2.1), fun e ↦ hw (e ▸ h.2.2)⟩
  | rccx0 _ _ _ => exact h.elim
  | rccx1 _ _ _ => exact h.elim
  | unxorList _ _ => exact h.elim
  | unquad _ _ _ => exact h.elim

/-- Every step of the list is tame. -/
def TameL (P : Wire n → Prop) (ss : List (Step n)) : Prop := ∀ s ∈ ss, Tame P s

theorem tameL_append {P : Wire n → Prop} {l₁ l₂ : List (Step n)} :
    TameL P (l₁ ++ l₂) ↔ TameL P l₁ ∧ TameL P l₂ := by
  simp only [TameL, List.mem_append, or_imp, forall_and]

theorem tameL_nil {P : Wire n → Prop} : TameL P ([] : List (Step n)) := fun s hs ↦ by
  simp at hs

theorem tameL_cons {P : Wire n → Prop} {s : Step n} {l : List (Step n)} :
    TameL P (s :: l) ↔ Tame P s ∧ TameL P l := by
  simp only [TameL, List.mem_cons, or_imp, forall_and, forall_eq]

theorem tameL_singleton {P : Wire n → Prop} {s : Step n} (h : Tame P s) :
    TameL P [s] := fun t ht ↦ by
  rw [List.mem_singleton] at ht; exact ht ▸ h

theorem tameL_copySteps {P : Wire n → Prop} : ∀ (k : ℕ) (s d : QRegister k n),
    (∀ i, P (s i)) → (∀ i, P (d i)) → TameL P (copySteps k s d) := by
  intro k
  induction k with
  | zero => intro s d _ _; exact tameL_nil
  | succ k ih =>
    intro s d hs hd
    rw [copySteps, tameL_cons]
    exact ⟨⟨hs 0, hd 0⟩, ih _ _ (fun i ↦ by rw [regTail_apply]; exact hs _)
      (fun i ↦ by rw [regTail_apply]; exact hd _)⟩

theorem tame_ctrlFlip {P : Wire n → Prop} {c : Option (Wire n)} (hc : ∀ q, c = some q → P q)
    {t : Wire n} (ht : P t) : Tame P (ctrlFlip c t) := by
  cases c with
  | none => exact ht
  | some c₀ => exact ⟨hc c₀ rfl, ht⟩

theorem tameL_xorSteps {P : Wire n → Prop} (c : Option (Wire n)) (hc : ∀ q, c = some q → P q) :
    ∀ (k : ℕ) (r : QRegister k n) (d : BitAssignment k), (∀ i, P (r i)) →
      TameL P (xorSteps c k r d) := by
  intro k
  induction k with
  | zero => intro r d _; exact tameL_nil
  | succ k ih =>
    intro r d hr
    rw [xorSteps, tameL_append]
    refine ⟨?_, ih _ _ (fun i ↦ by rw [regTail_apply]; exact hr _)⟩
    split_ifs
    · exact tameL_singleton (tame_ctrlFlip hc (hr 0))
    · exact tameL_nil

theorem tameL_ripple {P : Wire n → Prop} : ∀ (k : ℕ) (rA rB : QRegister (k + 1) n) (ci : Wire n)
    (rC : QRegister k n), (∀ i, P (rA i)) → (∀ i, P (rB i)) → P ci → (∀ i, P (rC i)) →
      TameL P (rippleSteps k rA rB ci rC) := by
  intro k
  induction k with
  | zero =>
    intro rA rB ci rC hA hB hci hC
    intro s hs
    simp only [rippleSteps, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨hA 0, hB 0⟩
    · exact ⟨hci, hB 0⟩
  | succ k ih =>
    intro rA rB ci rC hA hB hci hC
    have hA' : ∀ i, P (regTail rA i) := fun i ↦ by rw [regTail_apply]; exact hA _
    have hB' : ∀ i, P (regTail rB i) := fun i ↦ by rw [regTail_apply]; exact hB _
    have hC' : ∀ i, P (regTail rC i) := fun i ↦ by rw [regTail_apply]; exact hC _
    rw [rippleSteps, tameL_append, tameL_append]
    refine ⟨⟨?_, ih _ _ _ _ hA' hB' (hC 0) hC'⟩, ?_⟩
    · intro s hs
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl <;> simp only [Tame] <;>
        first | exact ⟨hci, hA 0⟩ | exact ⟨hci, hB 0⟩ | exact ⟨hA 0, hB 0, hC 0⟩ | exact ⟨hci, hC 0⟩
    · intro s hs
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl <;> simp only [Tame] <;>
        first | exact ⟨hci, hA 0⟩ | exact ⟨hA 0, hB 0⟩ | exact ⟨hA 0, hB 0, hC 0⟩ | exact ⟨hci, hC 0⟩

theorem tameL_caddc {P : Wire n → Prop} (w : ℕ) (rB rA : QRegister (w + 1) n)
    (rC : QRegister w n) (ci : Wire n) (c : Option (Wire n)) (d : ℕ)
    (hc : ∀ q, c = some q → P q) (hB : ∀ i, P (rB i)) (hA : ∀ i, P (rA i))
    (hC : ∀ i, P (rC i)) (hci : P ci) : TameL P (caddcSteps w rB rA rC ci c d) := by
  rw [caddcSteps, tameL_append, tameL_append]
  exact ⟨⟨tameL_xorSteps c hc _ _ _ hA, tameL_ripple w rA rB ci rC hA hB hci hC⟩,
    tameL_xorSteps c hc _ _ _ hA⟩

theorem tameL_modAdd {P : Wire n → Prop} (w p : ℕ) (rB rA : QRegister (w + 1) n)
    (rC : QRegister w n) (ci f e : Wire n) (cst : ℕ) (hB : ∀ i, P (rB i))
    (hA : ∀ i, P (rA i)) (hC : ∀ i, P (rC i)) (hci : P ci) (hf : P f) (he : P e) :
    TameL P (modAddSteps w p rB rA rC ci f e cst) := by
  have hK : ∀ (c : Option (Wire n)), (∀ q, c = some q → P q) → ∀ d : ℕ,
      TameL P (caddcSteps w rB rA rC ci c d) :=
    fun c hc d ↦ tameL_caddc w rB rA rC ci c d hc hB hA hC hci
  have hnone : ∀ q, (none : Option (Wire n)) = some q → P q := fun q h ↦ by cases h
  have hsome : ∀ x, P x → ∀ q, (some x : Option (Wire n)) = some q → P q :=
    fun x hx q h ↦ by cases h; exact hx
  simp only [modAddSteps, tameL_append]
  refine ⟨⟨⟨⟨⟨⟨hK _ (hsome e he) _, hK _ hnone _⟩, tameL_singleton ⟨hB _, hf⟩⟩,
    hK _ (hsome f hf) _⟩, hK _ (hsome e he) _⟩, ?_⟩, hK _ (hsome e he) _⟩
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact ⟨hB _, hf⟩
  · exact hf

theorem tameL_pair {P : Wire n → Prop} (w p : ℕ) (rX rY : QRegister w n)
    (rB rA : QRegister (w + 1) n) (rC : QRegister w n) (ci f g : Wire n)
    (hX : ∀ i, P (rX i)) (hY : ∀ i, P (rY i)) (hB : ∀ i, P (rB i)) (hA : ∀ i, P (rA i))
    (hC : ∀ i, P (rC i)) (hci : P ci) (hf : P f) (hg : P g) (i j : Fin w) :
    TameL P (pairSteps w p rX rY rB rA rC ci f g i j) := by
  simp only [pairSteps, tameL_append]
  exact ⟨⟨tameL_singleton ⟨hX i, hY j, hg⟩,
    tameL_modAdd w p rB rA rC ci f g _ hB hA hC hci hf hg⟩, tameL_singleton ⟨hX i, hY j, hg⟩⟩

theorem tameL_mul {P : Wire n → Prop} (w p : ℕ) (rX rY : QRegister w n)
    (rB rA : QRegister (w + 1) n) (rC : QRegister w n) (ci f g : Wire n)
    (hX : ∀ i, P (rX i)) (hY : ∀ i, P (rY i)) (hB : ∀ i, P (rB i)) (hA : ∀ i, P (rA i))
    (hC : ∀ i, P (rC i)) (hci : P ci) (hf : P f) (hg : P g) :
    TameL P (mulSteps w p rX rY rB rA rC ci f g) := by
  intro s hs
  simp only [mulSteps, List.mem_flatMap] at hs
  obtain ⟨i, _, j, _, hs⟩ := hs
  exact tameL_pair w p rX rY rB rA rC ci f g hX hY hB hA hC hci hf hg i j s hs

/-!
## Stage B2: a register file of `R` accumulators and a straight-line list of multiply-adds
-/

theorem disj_slice_left {k m : ℕ} {r : QRegister k n} {s : QRegister m n}
    (h : r.DisjointWires s) (o l : ℕ) (ho : o + l ≤ k) : (r.slice o l ho).DisjointWires s :=
  QRegister.disjoint_iff.2 fun i j ↦ by rw [QRegister.slice_apply]; exact h.ne _ _

theorem disj_slice_right {k m : ℕ} {r : QRegister k n} {s : QRegister m n}
    (h : r.DisjointWires s) (o l : ℕ) (ho : o + l ≤ m) : r.DisjointWires (s.slice o l ho) :=
  QRegister.disjoint_iff.2 fun i j ↦ by rw [QRegister.slice_apply]; exact h.ne _ _

/-- Disjointness facts for a register file `reg` of `w + 1` wire accumulators, the adder
workspace `rA`, `rC`, `ci`, and the single wires `f`, `g`. -/
structure Frame {w R : ℕ} (reg : Fin R → QRegister (w + 1) n) (rA : QRegister (w + 1) n)
    (rC : QRegister w n) (ci f g : Wire n) : Prop where
  regReg : ∀ j j', j ≠ j' → (reg j).DisjointWires (reg j')
  regA : ∀ j, (reg j).DisjointWires rA
  regC : ∀ j, (reg j).DisjointWires rC
  AC : rA.DisjointWires rC
  ciR : ∀ j, ci ∉ Set.range (reg j).wires
  fR : ∀ j, f ∉ Set.range (reg j).wires
  gR : ∀ j, g ∉ Set.range (reg j).wires
  ciA : ci ∉ Set.range rA.wires
  ciC : ci ∉ Set.range rC.wires
  fA : f ∉ Set.range rA.wires
  fC : f ∉ Set.range rC.wires
  gA : g ∉ Set.range rA.wires
  gC : g ∉ Set.range rC.wires
  cif : ci ≠ f
  cig : ci ≠ g
  fg : f ≠ g

/-- The `w` low wires of accumulator `j`, used as a multiplication operand. -/
def opd {w R : ℕ} (reg : Fin R → QRegister (w + 1) n) (j : Fin R) : QRegister w n :=
  (reg j).slice 0 w (by omega)

theorem Frame.wiring {w R : ℕ} {reg : Fin R → QRegister (w + 1) n} {rA : QRegister (w + 1) n}
    {rC : QRegister w n} {ci f g : Wire n} (hF : Frame reg rA rC ci f g) {d a b : Fin R}
    (hda : d ≠ a) (hdb : d ≠ b) (hab : a ≠ b) :
    Wiring (opd reg a) (opd reg b) (reg d) rA rC ci f g := by
  have hs : ∀ (j : Fin R) (q : Wire n), q ∉ Set.range (reg j).wires →
      q ∉ Set.range (opd reg j).wires := fun j q h ↦ not_mem_slice h _ _ _
  exact ⟨QRegister.disjoint_comm.1 (hF.regA d), hF.AC, hF.regC d,
    disj_slice_left (disj_slice_right (hF.regReg a b hab) _ _ _) _ _ _,
    disj_slice_left (hF.regA a) _ _ _,
    disj_slice_left (hF.regReg a d (Ne.symm hda)) _ _ _,
    disj_slice_left (hF.regC a) _ _ _,
    disj_slice_left (hF.regA b) _ _ _,
    disj_slice_left (hF.regReg b d (Ne.symm hdb)) _ _ _,
    disj_slice_left (hF.regC b) _ _ _,
    hF.ciA, hF.ciR d, hF.ciC, hs a _ (hF.ciR a), hs b _ (hF.ciR b),
    hF.fA, hF.fR d, hF.fC, hs a _ (hF.fR a), hs b _ (hF.fR b),
    hF.gA, hF.gR d, hF.gC, hs a _ (hF.gR a), hs b _ (hF.gR b),
    hF.cif, hF.cig, hF.fg⟩

variable {w p R : ℕ} (reg : Fin R → QRegister (w + 1) n) (rA : QRegister (w + 1) n)
  (rC : QRegister w n) (ci f g : Wire n)

/-- Register-file invariant: accumulator `j` holds `st j`, the adder workspace is clean and the
flag wires are zero. -/
def Inv (β : BitAssignment n) (st : Fin R → ZMod p) : Prop :=
  (∀ j i, β (reg j i) = natBits (w + 1) (st j).val i) ∧ Clean rA rC ci β ∧ β f = 0 ∧ β g = 0

theorem localIdx_opd [NeZero p] (hp : p < 2 ^ w) {β : BitAssignment n} {st : Fin R → ZMod p}
    {j : Fin R} (h : ∀ i, β (reg j i) = natBits (w + 1) (st j).val i) :
    (localIdx (opd reg j) β : ℕ) = (st j).val := by
  have hlt : (st j).val < 2 ^ w := (ZMod.val_lt _).trans hp
  have : localIdx (opd reg j) β = ⟨(st j).val, hlt⟩ := by
    rw [localIdx, Equiv.symm_apply_eq, basisBits_mk_eq_natBits]
    funext i
    show β ((reg j).slice 0 w _ i) = ((_ / 2 ^ (i : ℕ) % 2 : ℕ) : ZMod 2)
    rw [QRegister.slice_apply, h]
    show ((_ / 2 ^ (0 + (i : ℕ)) % 2 : ℕ) : ZMod 2) = _
    rw [Nat.zero_add]
  rw [this]

/-- One multiply-accumulate: `acc d ← acc d + acc a * acc b`. -/
abbrev Op (R : ℕ) : Type := Fin R × Fin R × Fin R

def OpOK {R : ℕ} (o : Op R) : Prop := o.1 ≠ o.2.1 ∧ o.1 ≠ o.2.2 ∧ o.2.1 ≠ o.2.2

def opSteps (o : Op R) : List (Step n) :=
  mulSteps w p (opd reg o.2.1) (opd reg o.2.2) (reg o.1) rA rC ci f g

def opsSteps (L : List (Op R)) : List (Step n) :=
  L.flatMap (opSteps (p := p) reg rA rC ci f g)

def evalOp (st : Fin R → ZMod p) (o : Op R) : Fin R → ZMod p :=
  update st o.1 (st o.1 + st o.2.1 * st o.2.2)

def evalOps (st : Fin R → ZMod p) (L : List (Op R)) : Fin R → ZMod p :=
  L.foldl evalOp st

theorem runList_op [NeZero p] (hF : Frame reg rA rC ci f g) (hp : p < 2 ^ w) {o : Op R}
    (ho : OpOK o) {β : BitAssignment n} {st : Fin R → ZMod p}
    (hI : Inv reg rA rC ci f g β st) :
    ∃ β', runList (opSteps (p := p) reg rA rC ci f g o) β = some β' ∧
      Inv reg rA rC ci f g β' (evalOp st o) := by
  obtain ⟨d, a, b⟩ := o
  obtain ⟨hda, hdb, hab⟩ := ho
  obtain ⟨hbits, hclean, hf0, hg0⟩ := hI
  have hp0 : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hβ : β = writeReg β (reg d) (natBits (w + 1) (st d).val) := by
    have : (fun i ↦ β (reg d i)) = natBits (w + 1) (st d).val := funext (hbits d)
    rw [← this, writeReg_self]
  have hrun := runList_mul (hF.wiring hda hdb hab) hp0 hp β hclean hf0 hg0 (st d).val
    (ZMod.val_lt _)
  rw [← hβ, localIdx_opd reg hp (hbits a), localIdx_opd reg hp (hbits b)] at hrun
  have hval : ((st d).val + (st a).val * (st b).val) % p = (st d + st a * st b).val := by
    rw [ZMod.val_add, ZMod.val_mul, Nat.add_mod_mod]
  rw [hval] at hrun
  refine ⟨_, hrun, ?_, ?_, ?_, ?_⟩
  · intro j i
    by_cases hj : j = d
    · subst hj
      rw [evalOp, update_self, writeReg_apply_reg]
    · rw [evalOp, update_of_ne hj, writeReg_apply_of_not_mem _ _ _ _
        (not_mem_of_disjoint (hF.regReg j d hj) i), hbits j i]
  · refine ⟨fun i ↦ ?_, fun i ↦ ?_, ?_⟩
    · rw [writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint
        (QRegister.disjoint_comm.1 (hF.regA d)) i), hclean.1 i]
    · rw [writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint
        (QRegister.disjoint_comm.1 (hF.regC d)) i), hclean.2.1 i]
    · rw [writeReg_apply_of_not_mem _ _ _ _ (hF.ciR d), hclean.2.2]
  · rw [writeReg_apply_of_not_mem _ _ _ _ (hF.fR d), hf0]
  · rw [writeReg_apply_of_not_mem _ _ _ _ (hF.gR d), hg0]

theorem runList_ops [NeZero p] (hF : Frame reg rA rC ci f g) (hp : p < 2 ^ w) :
    ∀ (L : List (Op R)), (∀ o ∈ L, OpOK o) → ∀ {β : BitAssignment n} {st : Fin R → ZMod p},
    Inv reg rA rC ci f g β st →
    ∃ β', runList (opsSteps (p := p) reg rA rC ci f g L) β = some β' ∧
      Inv reg rA rC ci f g β' (evalOps st L)
  | [], _, β, st, hI => ⟨β, by rw [opsSteps, List.flatMap_nil, runList_nil], hI⟩
  | o :: L, hL, β, st, hI => by
    obtain ⟨β1, h1, hI1⟩ := runList_op reg rA rC ci f g hF hp (hL o (List.mem_cons_self ..)) hI
    obtain ⟨β2, h2, hI2⟩ := runList_ops hF hp L (fun o' h ↦ hL o' (List.mem_cons_of_mem _ h)) hI1
    refine ⟨β2, ?_, hI2⟩
    rw [opsSteps, List.flatMap_cons, runList_append, h1, Option.bind_some]
    exact h2

theorem andCount_opsSteps (L : List (Op R)) :
    ((opsSteps (p := p) reg rA rC ci f g L).map Step.andCount).sum =
      L.length * (w * w * (5 * w + 1)) := by
  induction L with
  | nil => simp [opsSteps]
  | cons o L ih =>
    rw [opsSteps, List.flatMap_cons, List.map_append, List.sum_append, ← opsSteps, ih,
      opSteps, andCount_mul, List.length_cons]
    ring

theorem tameL_opsSteps {P : Wire n → Prop} (hR : ∀ j i, P (reg j i)) (hA : ∀ i, P (rA i))
    (hC : ∀ i, P (rC i)) (hci : P ci) (hf : P f) (hg : P g) (L : List (Op R)) :
    TameL P (opsSteps (p := p) reg rA rC ci f g L) := by
  intro s hs
  simp only [opsSteps, List.mem_flatMap] at hs
  obtain ⟨o, _, hs⟩ := hs
  exact tameL_mul w p _ _ _ _ _ ci f g (fun i ↦ hR _ _) (fun i ↦ hR _ _) (fun i ↦ hR _ _) hA
    hC hci hf hg s hs

/-!
## Stage B3: cost of the inverse list

`andCount` of an inverse step is `uCount` of the step: the `unand`s of the forward list become
`and4t`s of the inverse list.
-/

def uCount (s : Step n) : ℕ := s.inv.andCount

theorem andCount_inv_list (L : List (Step n)) :
    ((L.reverse.map Step.inv).map Step.andCount).sum = (L.map uCount).sum := by
  rw [List.map_map, List.map_reverse, List.sum_reverse]
  rfl

theorem uCount_ctrlFlip (c : Option (Wire n)) (t : Wire n) : uCount (ctrlFlip c t) = 0 := by
  cases c <;> rfl

theorem uCount_xorSteps (c : Option (Wire n)) (k : ℕ) (r : QRegister k n) (d : BitAssignment k) :
    ((xorSteps c k r d).map uCount).sum = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [xorSteps, List.map_append, List.sum_append, ih]
    split_ifs <;> simp [uCount_ctrlFlip]

theorem uCount_copySteps : ∀ (k : ℕ) (s d : QRegister k n),
    ((copySteps k s d).map uCount).sum = 0 := by
  intro k
  induction k with
  | zero => intro s d; rfl
  | succ k ih =>
    intro s d
    rw [copySteps, List.map_cons, List.sum_cons, ih]
    rfl

theorem uCount_ripple (k : ℕ) (rA rB : QRegister (k + 1) n) (ci : Wire n) (rC : QRegister k n) :
    ((rippleSteps k rA rB ci rC).map uCount).sum = k := by
  induction k generalizing ci with
  | zero => rfl
  | succ k ih =>
    rw [rippleSteps, List.map_append, List.map_append, List.sum_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, uCount, Step.inv,
      Step.andCount]
    omega

theorem uCount_caddc (w : ℕ) (rB rA : QRegister (w + 1) n) (rC : QRegister w n) (ci : Wire n)
    (c : Option (Wire n)) (d : ℕ) :
    ((caddcSteps w rB rA rC ci c d).map uCount).sum = w := by
  simp only [caddcSteps, List.map_append, List.sum_append, uCount_xorSteps, uCount_ripple,
    zero_add, add_zero]

theorem uCount_modAdd (w p : ℕ) (rB rA : QRegister (w + 1) n) (rC : QRegister w n)
    (ci f e : Wire n) (cst : ℕ) :
    ((modAddSteps w p rB rA rC ci f e cst).map uCount).sum = 5 * w := by
  simp only [modAddSteps, List.map_append, List.sum_append, uCount_caddc, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, uCount, Step.inv, Step.andCount]
  omega

theorem uCount_mul (w p : ℕ) (rX rY : QRegister w n) (rB rA : QRegister (w + 1) n)
    (rC : QRegister w n) (ci f g : Wire n) :
    ((mulSteps w p rX rY rB rA rC ci f g).map uCount).sum = w * w * (5 * w + 1) := by
  have hpair : ∀ i j, ((pairSteps w p rX rY rB rA rC ci f g i j).map uCount).sum =
      5 * w + 1 := fun i j ↦ by
    simp only [pairSteps, List.map_append, List.sum_append, uCount_modAdd, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, uCount, Step.inv, Step.andCount]
    omega
  have hflat : ∀ {α : Type} (L : List α) (F : α → List (Step n)) (c : ℕ),
      (∀ a, ((F a).map uCount).sum = c) →
      (((L.flatMap F).map uCount).sum = L.length * c) := by
    intro α L F c hF
    induction L with
    | nil => simp
    | cons a L ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, hF, ih, List.length_cons]
      ring
  unfold mulSteps
  rw [hflat (List.finRange w) _ (w * (5 * w + 1)), List.length_finRange, ← mul_assoc]
  intro i
  rw [hflat (List.finRange w) _ (5 * w + 1) (hpair i), List.length_finRange]

theorem uCount_opsSteps (L : List (Op R)) :
    ((opsSteps (p := p) reg rA rC ci f g L).map uCount).sum =
      L.length * (w * w * (5 * w + 1)) := by
  induction L with
  | nil => simp [opsSteps]
  | cons o L ih =>
    rw [opsSteps, List.flatMap_cons, List.map_append, List.sum_append, ← opsSteps, ih,
      opSteps, uCount_mul, List.length_cons]
    ring

/-!
## Stage C1: the layout of the ancilla register
-/

section Layout

variable {w : ℕ} (rAnc : QRegister (24 * w + 26) n)

theorem off_le (j j' w : ℕ) (h : j < j') : j * (w + 1) + (w + 1) ≤ j' * (w + 1) :=
  calc j * (w + 1) + (w + 1) = (j + 1) * (w + 1) := by ring
    _ ≤ j' * (w + 1) := Nat.mul_le_mul_right _ h

/-- Accumulator `j` of the register file: `w + 1` wires at offset `j * (w + 1)`. -/
def ancReg (j : Fin 22) : QRegister (w + 1) n :=
  rAnc.slice ((j : ℕ) * (w + 1)) (w + 1) (by
    have := off_le (j : ℕ) 22 w j.isLt
    omega)

def ancA : QRegister (w + 1) n := rAnc.slice (22 * (w + 1)) (w + 1) (by omega)
def ancC : QRegister w n := rAnc.slice (23 * (w + 1)) w (by omega)
def ancCi : Wire n := rAnc ⟨24 * w + 23, by omega⟩
def ancF : Wire n := rAnc ⟨24 * w + 24, by omega⟩
def ancG : Wire n := rAnc ⟨24 * w + 25, by omega⟩

theorem anc_frame :
    Frame (ancReg rAnc) (ancA rAnc) (ancC rAnc) (ancCi rAnc) (ancF rAnc) (ancG rAnc) := by
  have wne : ∀ a b : Fin (24 * w + 26), (a : ℕ) ≠ b → rAnc a ≠ rAnc b :=
    fun a b h hab ↦ h (congrArg Fin.val (rAnc.wires.injective hab))
  have hw : ∀ (q : ℕ) (hq : q < 24 * w + 26) (o l : ℕ) (h : o + l ≤ 24 * w + 26),
      o + l ≤ q → rAnc ⟨q, hq⟩ ∉ Set.range (rAnc.slice o l h).wires :=
    fun q hq o l h hle ↦ apply_not_mem_slice rAnc ⟨q, hq⟩ o l h (Or.inr hle)
  refine ⟨fun j j' hne ↦ ?_, fun j ↦ ?_, fun j ↦ ?_, ?_, fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact QRegister.slice_disjoint_of_le rAnc _ _ _ _ _ _ (off_le _ _ w h)
    · exact QRegister.disjoint_comm.1
        (QRegister.slice_disjoint_of_le rAnc _ _ _ _ _ _ (off_le _ _ w h))
  · exact QRegister.slice_disjoint_of_le rAnc _ _ _ _ _ _
      (by have := off_le (j : ℕ) 22 w j.isLt; omega)
  · exact QRegister.slice_disjoint_of_le rAnc _ _ _ _ _ _
      (by have := off_le (j : ℕ) 22 w j.isLt; omega)
  · exact QRegister.slice_disjoint_of_le rAnc _ _ _ _ _ _ (by omega)
  · exact hw (24 * w + 23) (by omega) _ _ _
      (by have := off_le (j : ℕ) 22 w j.isLt; omega)
  · exact hw (24 * w + 24) (by omega) _ _ _
      (by have := off_le (j : ℕ) 22 w j.isLt; omega)
  · exact hw (24 * w + 25) (by omega) _ _ _
      (by have := off_le (j : ℕ) 22 w j.isLt; omega)
  · exact hw (24 * w + 23) (by omega) _ _ _ (by omega)
  · exact hw (24 * w + 23) (by omega) _ _ _ (by omega)
  · exact hw (24 * w + 24) (by omega) _ _ _ (by omega)
  · exact hw (24 * w + 24) (by omega) _ _ _ (by omega)
  · exact hw (24 * w + 25) (by omega) _ _ _ (by omega)
  · exact hw (24 * w + 25) (by omega) _ _ _ (by omega)
  · exact wne _ _ (by show 24 * w + 23 ≠ 24 * w + 24; omega)
  · exact wne _ _ (by show 24 * w + 23 ≠ 24 * w + 25; omega)
  · exact wne _ _ (by show 24 * w + 24 ≠ 24 * w + 25; omega)

end Layout

/-!
## Stage C2: loading the register file, and the 22 operations
-/

section Load

variable {w p R : ℕ} (reg : Fin R → QRegister (w + 1) n) (rA : QRegister (w + 1) n)
  (rC : QRegister w n) (ci f g : Wire n)

theorem Inv_writeReg [NeZero p] (hF : Frame reg rA rC ci f g) {β : BitAssignment n}
    {st : Fin R → ZMod p} (hI : Inv reg rA rC ci f g β st) (d : Fin R) (c : ZMod p) :
    Inv reg rA rC ci f g (writeReg β (reg d) (natBits (w + 1) c.val)) (update st d c) := by
  obtain ⟨hbits, hclean, hf0, hg0⟩ := hI
  refine ⟨fun j i ↦ ?_, ⟨fun i ↦ ?_, fun i ↦ ?_, ?_⟩, ?_, ?_⟩
  · by_cases hj : j = d
    · subst hj
      rw [update_self, writeReg_apply_reg]
    · rw [update_of_ne hj, writeReg_apply_of_not_mem _ _ _ _
        (not_mem_of_disjoint (hF.regReg j d hj) i), hbits j i]
  · rw [writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint
      (QRegister.disjoint_comm.1 (hF.regA d)) i), hclean.1 i]
  · rw [writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint
      (QRegister.disjoint_comm.1 (hF.regC d)) i), hclean.2.1 i]
  · rw [writeReg_apply_of_not_mem _ _ _ _ (hF.ciR d), hclean.2.2]
  · rw [writeReg_apply_of_not_mem _ _ _ _ (hF.fR d), hf0]
  · rw [writeReg_apply_of_not_mem _ _ _ _ (hF.gR d), hg0]

/-- Loading a constant into a zero accumulator. -/
theorem runList_load [NeZero p] {β : BitAssignment n} {st : Fin R → ZMod p}
    (hI : Inv reg rA rC ci f g β st) (d : Fin R) (h0 : st d = 0) (c : ZMod p) :
    runList (xorSteps none (w + 1) (reg d) (natBits (w + 1) c.val)) β =
      some (writeReg β (reg d) (natBits (w + 1) c.val)) := by
  rw [runList_xorSteps none _ _ _ (fun i ↦ ctrlNe_none _) β]
  refine congrArg some (congrArg (writeReg β (reg d)) (funext fun i ↦ ?_))
  rw [hI.1 d i, h0]
  simp [natBits, ctrlVal]

theorem bits_of_localIdx {k : ℕ} (r : QRegister k n) (β : BitAssignment n) (m : ℕ)
    (hm : m < 2 ^ k) (h : (localIdx r β : ℕ) = m) : ∀ i, β (r i) = natBits k m i := by
  intro i
  have h1 : basisBits k (localIdx r β) i = β (r i) := by rw [localIdx, Equiv.apply_symm_apply]
  rw [← h1, show localIdx r β = ⟨m, hm⟩ from Fin.ext h, basisBits_mk_eq_natBits]

/-- Copying a `w`-bit input chunk into the low wires of a zero accumulator. -/
theorem runList_copyIn [NeZero p] (hF : Frame reg rA rC ci f g) {β : BitAssignment n}
    {st : Fin R → ZMod p} (hI : Inv reg rA rC ci f g β st) (d : Fin R) (h0 : st d = 0)
    (rX : QRegister w n) (hdisj : rX.DisjointWires (reg d)) (X : ZMod p) (hX : X.val < 2 ^ w)
    (hbX : ∀ i, β (rX i) = natBits w X.val i) :
    runList (copySteps w rX (opd reg d)) β =
      some (writeReg β (reg d) (natBits (w + 1) X.val)) := by
  have hd' : rX.DisjointWires (opd reg d) := disj_slice_right hdisj _ _ _
  rw [runList_copySteps w rX _ hd' β]
  refine congrArg some ?_
  funext q
  by_cases hq : q ∈ Set.range (reg d).wires
  · obtain ⟨i, rfl⟩ := hq
    rw [writeReg_apply_reg]
    by_cases hi : (i : ℕ) < w
    · have e : opd reg d ⟨i, hi⟩ = reg d i := by
        rw [opd, QRegister.slice_apply]
        exact congrArg (reg d) (Fin.ext (Nat.zero_add _))
      rw [← e, writeReg_apply_reg, e, hI.1 d i, h0, hbX ⟨i, hi⟩]
      simp [natBits]
    · have hn : reg d i ∉ Set.range (opd reg d).wires :=
        apply_not_mem_slice (reg d) i 0 w (by omega) (Or.inr (by omega))
      rw [writeReg_apply_of_not_mem _ _ _ _ hn, hI.1 d i, h0]
      have hiw : (i : ℕ) = w := by have := i.isLt; omega
      simp [natBits, hiw, Nat.div_eq_of_lt hX]
  · have hn : q ∉ Set.range (opd reg d).wires := not_mem_slice hq _ _ _
    rw [writeReg_apply_of_not_mem _ _ _ _ hq, writeReg_apply_of_not_mem _ _ _ _ hn]

end Load

instance {R : ℕ} : DecidablePred (OpOK : Op R → Prop) := fun o ↦
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The 22 multiply-accumulates of the inversion-free mixed addition. Register roles:
0 `X`, 1 `Y`, 2 `Z` (copies of the input), 3 `xQ`, 4 `yQ`, 5 `1`, 6 `-1`, then accumulators
7 `u = yQ Z - Y`, 8 `s = xQ Z - X`, 9 `u1 = u`, 10 `s1 = s`, 11 `u2 = u²`, 12 `s2 = s²`,
13 `s3 = s³`, 14 `u2 Z`, 15 `s2 X`, 16 `A = u² Z - s³ - 2 s² X`, 17 `X3 = s A`,
18 `t = s² X - A`, 19 `s3 Y`, 20 `Y3 = u t - s³ Y`, 21 `Z3 = s³ Z`. -/
def ecOps : List (Op 22) :=
  [(7, 4, 2), (7, 6, 1), (8, 3, 2), (8, 6, 0), (9, 5, 7), (10, 5, 8), (11, 7, 9), (12, 8, 10),
   (13, 12, 8), (14, 11, 2), (15, 12, 0), (16, 5, 14), (16, 6, 13), (16, 6, 15), (16, 6, 15),
   (17, 8, 16), (18, 5, 15), (18, 6, 16), (19, 13, 1), (20, 7, 18), (20, 6, 19), (21, 13, 2)]

theorem ecOps_ok : ∀ o ∈ ecOps, OpOK o := by
  intro o ho
  simp only [ecOps, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem ecOps_length : ecOps.length = 22 := rfl

/-- The register file right after loading. -/
def initSt {p : ℕ} (X Y Z xQ yQ : ZMod p) : Fin 22 → ZMod p :=
  update (update (update (update (update (update (update (fun _ ↦ 0) 0 X) 1 Y) 2 Z) 3 xQ) 4 yQ)
    5 1) 6 (-1)

theorem evalOps_ecOps {p : ℕ} (X Y Z xQ yQ : ZMod p) :
    evalOps (initSt X Y Z xQ yQ) ecOps 17 = (projAddFn xQ yQ (X, Y, Z)).1 ∧
    evalOps (initSt X Y Z xQ yQ) ecOps 20 = (projAddFn xQ yQ (X, Y, Z)).2.1 ∧
    evalOps (initSt X Y Z xQ yQ) ecOps 21 = (projAddFn xQ yQ (X, Y, Z)).2.2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp [evalOps, ecOps, evalOp, initSt, update, projAddFn]
    ring

/-!
## Stage C3: the program, its setup, and the data register
-/

/-- A run of steps that all avoid a register leaves that register unchanged. -/
theorem runList_preserve {k : ℕ} (ss : List (Step n)) (r : QRegister k n)
    (h : ∀ s ∈ ss, ∀ i, s.Avoids (r i)) {β γ : BitAssignment n} (hs : runList ss β = some γ)
    (i : Fin k) : γ (r i) = β (r i) := by
  have e := runList_writeReg_of_avoids ss r h β (fun i ↦ β (r i))
  rw [writeReg_self, hs] at e
  simp only [Option.map_some] at e
  have e2 := congrFun (Option.some.inj e) (r i)
  rw [writeReg_apply_reg] at e2
  exact e2

/-- The `k`-th `w`-wire chunk of the `6 * w` data wires. -/
def dChunk {w : ℕ} (rData : QRegister (2 * (3 * w)) n) (k : Fin 6) : QRegister w n :=
  rData.slice (k * w) w (by
    have h := Nat.mul_le_mul_right w (show (k : ℕ) ≤ 5 by omega)
    omega)

theorem dChunk_apply {w : ℕ} (rData : QRegister (2 * (3 * w)) n) (k : Fin 6) (i : Fin w) :
    dChunk rData k i = rData ⟨k * w + i, by
      have h := Nat.mul_le_mul_right w (show (k : ℕ) ≤ 5 by omega)
      have := i.isLt
      omega⟩ :=
  QRegister.slice_apply _ _ _ _ _

theorem mem_range_slice {N : ℕ} (r : QRegister N n) (o l : ℕ) (h : o + l ≤ N) (i : Fin l) :
    (r.slice o l h) i ∈ Set.range r.wires :=
  ⟨_, (QRegister.slice_apply r o l h i).symm⟩

theorem chunk_disj_anc {w : ℕ} {rData : QRegister (2 * (3 * w)) n}
    {rAnc : QRegister (24 * w + 26) n} (hdisj : rData.DisjointWires rAnc) (k : Fin 6)
    (d : Fin 22) : (dChunk rData k).DisjointWires (ancReg rAnc d) :=
  disj_slice_right (disj_slice_left hdisj _ _ _) _ _ _

theorem chunk_disj_opd {w : ℕ} {rData : QRegister (2 * (3 * w)) n}
    {rAnc : QRegister (24 * w + 26) n} (hdisj : rData.DisjointWires rAnc) (k : Fin 6)
    (d : Fin 22) : (dChunk rData k).DisjointWires (opd (ancReg rAnc) d) :=
  disj_slice_right (chunk_disj_anc hdisj k d) _ _ _

/-- The setup: copy the input triple into registers 0, 1, 2 and load the constants. -/
def setupSteps {w p : ℕ} (xQ yQ : ZMod p) (rData : QRegister (2 * (3 * w)) n)
    (rAnc : QRegister (24 * w + 26) n) : List (Step n) :=
  copySteps w (dChunk rData 0) (opd (ancReg rAnc) 0) ++
  (copySteps w (dChunk rData 1) (opd (ancReg rAnc) 1) ++
  (copySteps w (dChunk rData 2) (opd (ancReg rAnc) 2) ++
  (xorSteps none (w + 1) (ancReg rAnc 3) (natBits (w + 1) xQ.val) ++
  (xorSteps none (w + 1) (ancReg rAnc 4) (natBits (w + 1) yQ.val) ++
  (xorSteps none (w + 1) (ancReg rAnc 5) (natBits (w + 1) (1 : ZMod p).val) ++
   xorSteps none (w + 1) (ancReg rAnc 6) (natBits (w + 1) (-1 : ZMod p).val))))))

theorem inv_init {w p : ℕ} (rAnc : QRegister (24 * w + 26) n) {β : BitAssignment n}
    (hβ : localIdx rAnc β = 0) :
    Inv (ancReg rAnc) (ancA rAnc) (ancC rAnc) (ancCi rAnc) (ancF rAnc) (ancG rAnc) β
      (fun _ : Fin 22 ↦ (0 : ZMod p)) := by
  have hz := anc_bits_zero rAnc β hβ
  refine ⟨fun j i ↦ ?_, ⟨fun i ↦ ?_, fun i ↦ ?_, ?_⟩, ?_, ?_⟩
  · rw [ancReg, QRegister.slice_apply, hz]; simp [natBits]
  · rw [ancA, QRegister.slice_apply, hz]
  · rw [ancC, QRegister.slice_apply, hz]
  · exact hz _
  · exact hz _
  · exact hz _

/-- Copy an input chunk into register `d` and keep the data chunks intact. -/
theorem setup_copy {w p : ℕ} [NeZero p] (rData : QRegister (2 * (3 * w)) n)
    (rAnc : QRegister (24 * w + 26) n) (hdisj : rData.DisjointWires rAnc)
    {β : BitAssignment n} {st : Fin 22 → ZMod p}
    (hI : Inv (ancReg rAnc) (ancA rAnc) (ancC rAnc) (ancCi rAnc) (ancF rAnc) (ancG rAnc) β st)
    (d : Fin 22) (h0 : st d = 0) (k : Fin 6) (X : ZMod p) (hX : X.val < 2 ^ w)
    (hbX : ∀ i, β (dChunk rData k i) = natBits w X.val i) :
    ∃ β', runList (copySteps w (dChunk rData k) (opd (ancReg rAnc) d)) β = some β' ∧
      Inv (ancReg rAnc) (ancA rAnc) (ancC rAnc) (ancCi rAnc) (ancF rAnc) (ancG rAnc) β'
        (update st d X) ∧ ∀ k' i, β' (dChunk rData k' i) = β (dChunk rData k' i) := by
  refine ⟨_, runList_copyIn (ancReg rAnc) (ancA rAnc) (ancC rAnc) (ancCi rAnc) (ancF rAnc)
    (ancG rAnc) (anc_frame rAnc) hI d h0 (dChunk rData k) (chunk_disj_anc hdisj k d) X hX hbX,
    ?_, fun k' i ↦ ?_⟩
  · exact Inv_writeReg (ancReg rAnc) (ancA rAnc) (ancC rAnc) (ancCi rAnc) (ancF rAnc)
      (ancG rAnc) (anc_frame rAnc) hI d X
  · exact writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint (chunk_disj_anc hdisj k' d) i)

/-- Load a constant into register `d` and keep the data chunks intact. -/
theorem setup_load {w p : ℕ} [NeZero p] (rData : QRegister (2 * (3 * w)) n)
    (rAnc : QRegister (24 * w + 26) n) (hdisj : rData.DisjointWires rAnc)
    {β : BitAssignment n} {st : Fin 22 → ZMod p}
    (hI : Inv (ancReg rAnc) (ancA rAnc) (ancC rAnc) (ancCi rAnc) (ancF rAnc) (ancG rAnc) β st)
    (d : Fin 22) (h0 : st d = 0) (c : ZMod p) :
    ∃ β', runList (xorSteps none (w + 1) (ancReg rAnc d) (natBits (w + 1) c.val)) β = some β' ∧
      Inv (ancReg rAnc) (ancA rAnc) (ancC rAnc) (ancCi rAnc) (ancF rAnc) (ancG rAnc) β'
        (update st d c) ∧ ∀ k' i, β' (dChunk rData k' i) = β (dChunk rData k' i) := by
  refine ⟨_, runList_load (ancReg rAnc) (ancA rAnc) (ancC rAnc) (ancCi rAnc) (ancF rAnc)
    (ancG rAnc) hI d h0 c, ?_, fun k' i ↦ ?_⟩
  · exact Inv_writeReg (ancReg rAnc) (ancA rAnc) (ancC rAnc) (ancCi rAnc) (ancF rAnc)
      (ancG rAnc) (anc_frame rAnc) hI d c
  · exact writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint (chunk_disj_anc hdisj k' d) i)

theorem runList_setup {w p : ℕ} [NeZero p] (hp : p < 2 ^ w) (xQ yQ X Y Z : ZMod p)
    (rData : QRegister (2 * (3 * w)) n) (rAnc : QRegister (24 * w + 26) n)
    (hdisj : rData.DisjointWires rAnc) {β : BitAssignment n} (hβ : localIdx rAnc β = 0)
    (hbX : ∀ i, β (dChunk rData 0 i) = natBits w X.val i)
    (hbY : ∀ i, β (dChunk rData 1 i) = natBits w Y.val i)
    (hbZ : ∀ i, β (dChunk rData 2 i) = natBits w Z.val i) :
    ∃ β', runList (setupSteps xQ yQ rData rAnc) β = some β' ∧
      Inv (ancReg rAnc) (ancA rAnc) (ancC rAnc) (ancCi rAnc) (ancF rAnc) (ancG rAnc) β'
        (initSt X Y Z xQ yQ) := by
  have hX : X.val < 2 ^ w := (ZMod.val_lt X).trans hp
  have hY : Y.val < 2 ^ w := (ZMod.val_lt Y).trans hp
  have hZ : Z.val < 2 ^ w := (ZMod.val_lt Z).trans hp
  obtain ⟨β1, h1, I1, d1⟩ := setup_copy rData rAnc hdisj (inv_init rAnc hβ) 0 rfl 0 X hX hbX
  obtain ⟨β2, h2, I2, d2⟩ := setup_copy rData rAnc hdisj I1 1 (by simp [update]) 1 Y hY
    (fun i ↦ (d1 1 i).trans (hbY i))
  obtain ⟨β3, h3, I3, d3⟩ := setup_copy rData rAnc hdisj I2 2 (by simp [update]) 2 Z hZ
    (fun i ↦ (d2 2 i).trans ((d1 2 i).trans (hbZ i)))
  obtain ⟨β4, h4, I4, -⟩ := setup_load rData rAnc hdisj I3 3 (by simp [update]) xQ
  obtain ⟨β5, h5, I5, -⟩ := setup_load rData rAnc hdisj I4 4 (by simp [update]) yQ
  obtain ⟨β6, h6, I6, -⟩ := setup_load rData rAnc hdisj I5 5 (by simp [update]) 1
  obtain ⟨β7, h7, I7, -⟩ := setup_load rData rAnc hdisj I6 6 (by simp [update]) (-1)
  refine ⟨β7, ?_, I7⟩
  simp only [setupSteps, runList_append, h1, h2, h3, h4, h5, h6, h7, Option.bind_some]

/-- The wires the compute phase touches: the ancillas and the three input chunks. -/
def PW {w : ℕ} (rData : QRegister (2 * (3 * w)) n) (rAnc : QRegister (24 * w + 26) n)
    (q : Wire n) : Prop :=
  q ∈ Set.range rAnc.wires ∨ ∃ j : Fin (2 * (3 * w)), (j : ℕ) < 3 * w ∧ rData j = q

theorem pw_anc {w : ℕ} (rData : QRegister (2 * (3 * w)) n) (rAnc : QRegister (24 * w + 26) n)
    (d : Fin 22) (i : Fin (w + 1)) : PW rData rAnc (ancReg rAnc d i) :=
  Or.inl (mem_range_slice rAnc _ _ _ i)

theorem pw_opd {w : ℕ} (rData : QRegister (2 * (3 * w)) n) (rAnc : QRegister (24 * w + 26) n)
    (d : Fin 22) (i : Fin w) : PW rData rAnc (opd (ancReg rAnc) d i) :=
  Or.inl (by simp only [opd, ancReg, QRegister.slice_apply]; exact ⟨_, rfl⟩)

theorem pw_in {w : ℕ} (rData : QRegister (2 * (3 * w)) n) (rAnc : QRegister (24 * w + 26) n)
    (k : Fin 6) (hk : (k : ℕ) < 3) (i : Fin w) : PW rData rAnc (dChunk rData k i) := by
  refine Or.inr ⟨⟨k * w + i, ?_⟩, ?_, (dChunk_apply rData k i).symm⟩
  · have h := Nat.mul_le_mul_right w (show (k : ℕ) ≤ 5 by omega)
    have := i.isLt
    omega
  · have h := Nat.mul_le_mul_right w (show (k : ℕ) ≤ 2 by omega)
    have := i.isLt
    show (k : ℕ) * w + i < 3 * w
    omega

theorem not_pw_out {w : ℕ} {rData : QRegister (2 * (3 * w)) n} {rAnc : QRegister (24 * w + 26) n}
    (hdisj : rData.DisjointWires rAnc) (k : Fin 6) (hk : 3 ≤ (k : ℕ)) (i : Fin w) :
    ¬ PW rData rAnc (dChunk rData k i) := by
  rintro (h | ⟨j, hj, hjq⟩)
  · rw [dChunk_apply] at h
    exact not_mem_of_disjoint hdisj _ h
  · rw [dChunk_apply] at hjq
    have := congrArg Fin.val (rData.wires.injective hjq)
    have h3 := Nat.mul_le_mul_right w hk
    change (j : ℕ) = k * w + i at this
    omega

theorem tameL_setup {w p : ℕ} (xQ yQ : ZMod p) (rData : QRegister (2 * (3 * w)) n)
    (rAnc : QRegister (24 * w + 26) n) : TameL (PW rData rAnc) (setupSteps xQ yQ rData rAnc) := by
  have hc : ∀ q : Wire n, (none : Option (Wire n)) = some q → PW rData rAnc q :=
    fun q h ↦ nomatch h
  unfold setupSteps
  refine tameL_append.2 ⟨tameL_copySteps _ _ _ (pw_in rData rAnc 0 (by decide))
    (pw_opd rData rAnc 0), tameL_append.2 ⟨tameL_copySteps _ _ _ (pw_in rData rAnc 1 (by decide))
    (pw_opd rData rAnc 1), tameL_append.2 ⟨tameL_copySteps _ _ _ (pw_in rData rAnc 2 (by decide))
    (pw_opd rData rAnc 2), tameL_append.2 ⟨tameL_xorSteps none hc _ _ _ (pw_anc rData rAnc 3),
    tameL_append.2 ⟨tameL_xorSteps none hc _ _ _ (pw_anc rData rAnc 4),
    tameL_append.2 ⟨tameL_xorSteps none hc _ _ _ (pw_anc rData rAnc 5),
    tameL_xorSteps none hc _ _ _ (pw_anc rData rAnc 6)⟩⟩⟩⟩⟩⟩

/-- The compute phase `C`. -/
def ecC {w p : ℕ} (xQ yQ : ZMod p) (rData : QRegister (2 * (3 * w)) n)
    (rAnc : QRegister (24 * w + 26) n) : List (Step n) :=
  setupSteps xQ yQ rData rAnc ++
    opsSteps (p := p) (ancReg rAnc) (ancA rAnc) (ancC rAnc) (ancCi rAnc) (ancF rAnc) (ancG rAnc)
      ecOps

theorem tameL_ecC {w p : ℕ} (xQ yQ : ZMod p) (rData : QRegister (2 * (3 * w)) n)
    (rAnc : QRegister (24 * w + 26) n) : TameL (PW rData rAnc) (ecC xQ yQ rData rAnc) := by
  refine tameL_append.2 ⟨tameL_setup xQ yQ rData rAnc, ?_⟩
  exact tameL_opsSteps (ancReg rAnc) (ancA rAnc) (ancC rAnc) (ancCi rAnc) (ancF rAnc)
    (ancG rAnc) (fun j i ↦ pw_anc rData rAnc j i) (fun i ↦ Or.inl (mem_range_slice rAnc _ _ _ i))
    (fun i ↦ Or.inl (mem_range_slice rAnc _ _ _ i)) (Or.inl ⟨_, rfl⟩) (Or.inl ⟨_, rfl⟩)
    (Or.inl ⟨_, rfl⟩) ecOps

/-- Copy the three result registers into the output chunks of the data register. -/
def copyOutSteps {w : ℕ} (rData : QRegister (2 * (3 * w)) n) (rAnc : QRegister (24 * w + 26) n) :
    List (Step n) :=
  copySteps w (opd (ancReg rAnc) 17) (dChunk rData 3) ++
  (copySteps w (opd (ancReg rAnc) 20) (dChunk rData 4) ++
   copySteps w (opd (ancReg rAnc) 21) (dChunk rData 5))

/-- The full program: compute, copy the result out, uncompute. -/
def ecAddProjSteps {w p : ℕ} (xQ yQ : ZMod p) (rData : QRegister (2 * (3 * w)) n)
    (rAnc : QRegister (24 * w + 26) n) : List (Step n) :=
  ecC xQ yQ rData rAnc ++ (copyOutSteps rData rAnc ++ (ecC xQ yQ rData rAnc).reverse.map Step.inv)

theorem chunk_disj {w : ℕ} (rData : QRegister (2 * (3 * w)) n) (k k' : Fin 6)
    (h : (k : ℕ) < k') : (dChunk rData k).DisjointWires (dChunk rData k') :=
  QRegister.slice_disjoint_of_le rData _ _ _ _ _ _ (by
    have h1 := Nat.mul_le_mul_right w (show (k : ℕ) + 1 ≤ k' by omega)
    rw [Nat.add_mul, Nat.one_mul] at h1
    exact h1)

/-- One copy of a result register into an output chunk that currently holds zero. -/
theorem run_copyOut {w : ℕ} {rData : QRegister (2 * (3 * w)) n}
    {rAnc : QRegister (24 * w + 26) n} (hdisj : rData.DisjointWires rAnc) (d : Fin 22)
    (k : Fin 6) (v : ℕ) {δ : BitAssignment n} (h0 : ∀ i, δ (dChunk rData k i) = 0)
    (hv : ∀ i, δ (opd (ancReg rAnc) d i) = natBits w v i) :
    runList (copySteps w (opd (ancReg rAnc) d) (dChunk rData k)) δ =
      some (writeReg δ (dChunk rData k) (natBits w v)) := by
  rw [runList_copySteps w _ _ (QRegister.disjoint_comm.1 (chunk_disj_opd hdisj k d))]
  refine congrArg some (congrArg (writeReg δ (dChunk rData k)) (funext fun i ↦ ?_))
  rw [h0 i, hv i, zero_add]

theorem runList_prog {w p : ℕ} [NeZero p] (hp : p < 2 ^ w) (xQ yQ X Y Z : ZMod p)
    (rData : QRegister (2 * (3 * w)) n) (rAnc : QRegister (24 * w + 26) n)
    (hdisj : rData.DisjointWires rAnc) {β : BitAssignment n} (hβ : localIdx rAnc β = 0)
    (hbX : ∀ i, β (dChunk rData 0 i) = natBits w X.val i)
    (hbY : ∀ i, β (dChunk rData 1 i) = natBits w Y.val i)
    (hbZ : ∀ i, β (dChunk rData 2 i) = natBits w Z.val i)
    (h3 : ∀ i, β (dChunk rData 3 i) = 0) (h4 : ∀ i, β (dChunk rData 4 i) = 0)
    (h5 : ∀ i, β (dChunk rData 5 i) = 0) :
    runList (ecAddProjSteps xQ yQ rData rAnc) β =
      some (writeReg (writeReg (writeReg β (dChunk rData 3)
        (natBits w (projAddFn xQ yQ (X, Y, Z)).1.val)) (dChunk rData 4)
        (natBits w (projAddFn xQ yQ (X, Y, Z)).2.1.val)) (dChunk rData 5)
        (natBits w (projAddFn xQ yQ (X, Y, Z)).2.2.val)) := by
  obtain ⟨e17, e20, e21⟩ := evalOps_ecOps X Y Z xQ yQ
  rw [← e17, ← e20, ← e21]
  obtain ⟨β1, hs1, I1⟩ := runList_setup hp xQ yQ X Y Z rData rAnc hdisj hβ hbX hbY hbZ
  obtain ⟨γ, hops, I2⟩ := runList_ops (ancReg rAnc) (ancA rAnc) (ancC rAnc) (ancCi rAnc)
    (ancF rAnc) (ancG rAnc) (anc_frame rAnc) hp ecOps ecOps_ok I1
  have hC : runList (ecC xQ yQ rData rAnc) β = some γ := by
    rw [ecC, runList_append, hs1, Option.bind_some, hops]
  have hT := tameL_ecC xQ yQ rData rAnc
  have hav : ∀ k : Fin 6, 3 ≤ (k : ℕ) → ∀ s ∈ ecC xQ yQ rData rAnc, ∀ i,
      s.Avoids (dChunk rData k i) := fun k hk s hs i ↦ (hT s hs).avoids (not_pw_out hdisj k hk i)
  have hav' : ∀ k : Fin 6, 3 ≤ (k : ℕ) → ∀ s ∈ (ecC xQ yQ rData rAnc).reverse.map Step.inv,
      ∀ i, s.Avoids (dChunk rData k i) := by
    intro k hk s hs i
    simp only [List.mem_map, List.mem_reverse] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact Step.avoids_inv (hav k hk t ht i)
  have hpres : ∀ k : Fin 6, 3 ≤ (k : ℕ) → ∀ i, γ (dChunk rData k i) = β (dChunk rData k i) :=
    fun k hk i ↦ runList_preserve _ (dChunk rData k) (hav k hk) hC i
  have hb : ∀ d : Fin 22, ∀ i, γ (opd (ancReg rAnc) d i) =
      natBits w (evalOps (initSt X Y Z xQ yQ) ecOps d).val i := fun d ↦
    bits_of_localIdx _ γ _ ((ZMod.val_lt _).trans hp)
      (localIdx_opd (ancReg rAnc) hp (fun i ↦ I2.1 d i))
  have hd3 : (dChunk rData 3).DisjointWires (dChunk rData 4) := chunk_disj rData 3 4 (by decide)
  have hd4 : (dChunk rData 3).DisjointWires (dChunk rData 5) := chunk_disj rData 3 5 (by decide)
  have hd5 : (dChunk rData 4).DisjointWires (dChunk rData 5) := chunk_disj rData 4 5 (by decide)
  have hcopy : runList (copyOutSteps rData rAnc) γ = some (writeReg (writeReg (writeReg γ
      (dChunk rData 3) (natBits w (evalOps (initSt X Y Z xQ yQ) ecOps 17).val)) (dChunk rData 4)
      (natBits w (evalOps (initSt X Y Z xQ yQ) ecOps 20).val)) (dChunk rData 5)
      (natBits w (evalOps (initSt X Y Z xQ yQ) ecOps 21).val)) := by
    rw [copyOutSteps, runList_append,
      run_copyOut hdisj 17 3 _ (fun i ↦ (hpres 3 (by decide) i).trans (h3 i)) (hb 17),
      Option.bind_some, runList_append,
      run_copyOut hdisj 20 4 _ (fun i ↦ by
        rw [writeReg_apply_of_not_mem _ _ _ _
          (not_mem_of_disjoint (QRegister.disjoint_comm.1 hd3) i),
          hpres 4 (by decide) i, h4 i])
        (fun i ↦ by
          rw [writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint
            (QRegister.disjoint_comm.1 (chunk_disj_opd hdisj 3 20)) i), hb 20 i]),
      Option.bind_some]
    exact run_copyOut hdisj 21 5 _ (fun i ↦ by
        rw [writeReg_apply_of_not_mem _ _ _ _
            (not_mem_of_disjoint (QRegister.disjoint_comm.1 hd5) i),
          writeReg_apply_of_not_mem _ _ _ _
            (not_mem_of_disjoint (QRegister.disjoint_comm.1 hd4) i),
          hpres 5 (by decide) i, h5 i])
      (fun i ↦ by
        rw [writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint
            (QRegister.disjoint_comm.1 (chunk_disj_opd hdisj 4 21)) i),
          writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint
            (QRegister.disjoint_comm.1 (chunk_disj_opd hdisj 3 21)) i), hb 21 i])
  have hinv : runList ((ecC xQ yQ rData rAnc).reverse.map Step.inv) γ = some β :=
    runList_inv (fun s hs ↦ (hT s hs).noUnxor) hC
  have hpresβ : ∀ k : Fin 6, 3 ≤ (k : ℕ) → ∀ i, γ (dChunk rData k i) = β (dChunk rData k i) :=
    hpres
  rw [ecAddProjSteps, runList_append, hC, Option.bind_some, runList_append, hcopy,
    Option.bind_some, runList_writeReg_of_avoids _ (dChunk rData 5) (hav' 5 (by decide)),
    runList_writeReg_of_avoids _ (dChunk rData 4) (hav' 4 (by decide)),
    runList_writeReg_of_avoids _ (dChunk rData 3) (hav' 3 (by decide)), hinv]
  simp only [Option.map_some]

/-!
## Stage C4: the data register in base `2^w` digits
-/

/-- Six base-`t` digits, least significant first. -/
def nest6 (t a0 a1 a2 a3 a4 a5 : ℕ) : ℕ :=
  a0 + t * (a1 + t * (a2 + t * (a3 + t * (a4 + t * a5))))

theorem nest6_inj {t a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : ℕ} (h0 : a0 < t) (h1 : a1 < t)
    (h2 : a2 < t) (h3 : a3 < t) (h4 : a4 < t) (g0 : b0 < t) (g1 : b1 < t) (g2 : b2 < t)
    (g3 : b3 < t) (g4 : b4 < t) (h : nest6 t a0 a1 a2 a3 a4 a5 = nest6 t b0 b1 b2 b3 b4 b5) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 := by
  unfold nest6 at h
  obtain ⟨e0, h⟩ := pair_inj h0 g0 h
  obtain ⟨e1, h⟩ := pair_inj h1 g1 h
  obtain ⟨e2, h⟩ := pair_inj h2 g2 h
  obtain ⟨e3, h⟩ := pair_inj h3 g3 h
  obtain ⟨e4, e5⟩ := pair_inj h4 g4 h
  exact ⟨e0, e1, e2, e3, e4, e5⟩

theorem localIdx_slice_split {N : ℕ} (r : QRegister N n) (o l m L : ℕ) (hL : l + m = L)
    (h : o + L ≤ N) (β : BitAssignment n) :
    (localIdx (r.slice o L h) β : ℕ) = (localIdx (r.slice o l (by omega)) β : ℕ) +
      2 ^ l * (localIdx (r.slice (o + l) m (by omega)) β : ℕ) := by
  have h1 := localIdx_val_split (r.slice o L h) l m hL β
  rw [localIdx_slice_slice, localIdx_slice_slice] at h1
  exact h1

theorem localIdx_slice_congr {N : ℕ} (r : QRegister N n) {o o' l : ℕ} (h : o + l ≤ N)
    (h' : o' + l ≤ N) (e : o = o') (β : BitAssignment n) :
    localIdx (r.slice o l h) β = localIdx (r.slice o' l h') β := by
  subst e; rfl

theorem localIdx_nest6 {w : ℕ} (rData : QRegister (2 * (3 * w)) n) (β : BitAssignment n) :
    (localIdx rData β : ℕ) = nest6 (2 ^ w) (localIdx (dChunk rData 0) β)
      (localIdx (dChunk rData 1) β) (localIdx (dChunk rData 2) β) (localIdx (dChunk rData 3) β)
      (localIdx (dChunk rData 4) β) (localIdx (dChunk rData 5) β) := by
  have e : ∀ (k : Fin 6) (o : ℕ) (h : o + w ≤ 2 * (3 * w)) (he : o = k * w),
      localIdx (rData.slice o w h) β = localIdx (dChunk rData k) β :=
    fun k o h he ↦ localIdx_slice_congr rData h _ he β
  rw [localIdx_val_split rData w (5 * w) (by omega) β,
    localIdx_slice_split rData w w (4 * w) (5 * w) (by omega) (by omega) β,
    localIdx_slice_split rData (w + w) w (3 * w) (4 * w) (by omega) (by omega) β,
    localIdx_slice_split rData (w + w + w) w (2 * w) (3 * w) (by omega) (by omega) β,
    localIdx_slice_split rData (w + w + w + w) w w (2 * w) (by omega) (by omega) β,
    e 0 0 _ (by show 0 = 0 * w; omega), e 1 w _ (by show w = 1 * w; omega),
    e 2 (w + w) _ (by show w + w = 2 * w; omega),
    e 3 (w + w + w) _ (by show w + w + w = 3 * w; omega),
    e 4 (w + w + w + w) _ (by show w + w + w + w = 4 * w; omega),
    e 5 (w + w + w + w + w) _ (by show w + w + w + w + w = 5 * w; omega)]
  simp only [nest6]

theorem ecProjEncode_val {w p : ℕ} [NeZero p] (hhi : p ≤ 2 ^ w) (X Y Z : ZMod p) :
    ((ecProjEncode w (X, Y, Z)).val : ℕ) = X.val + 2 ^ w * (Y.val + 2 ^ w * Z.val) := by
  have h2 : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by rw [two_mul, pow_add]
  have h3 : 2 ^ (3 * w) = 2 ^ w * 2 ^ w * 2 ^ w := by
    rw [show 3 * w = w + w + w by omega, pow_add, pow_add]
  have hlt : ∀ z : ZMod p, z.val < 2 ^ w := fun z ↦ lt_of_lt_of_le (ZMod.val_lt z) hhi
  have h1 : 2 ^ w * (Z.val + 1) ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul_left _ (hlt Z)
  have hYZ : Y.val + 2 ^ w * Z.val < 2 ^ w * 2 ^ w := by
    have := hlt Y
    rw [mul_add, mul_one] at h1
    linarith
  have h4 : 2 ^ w * (Y.val + 2 ^ w * Z.val + 1) ≤ 2 ^ w * (2 ^ w * 2 ^ w) :=
    Nat.mul_le_mul_left _ hYZ
  have hb : X.val + 2 ^ w * (Y.val + 2 ^ w * Z.val) < 2 ^ (3 * w) := by
    have := hlt X
    rw [h3]
    rw [mul_add, mul_one] at h4
    linarith
  show (X.val + 2 ^ w * Y.val + 2 ^ (2 * w) * Z.val) % 2 ^ (3 * w) = _
  rw [show X.val + 2 ^ w * Y.val + 2 ^ (2 * w) * Z.val =
      X.val + 2 ^ w * (Y.val + 2 ^ w * Z.val) by rw [h2]; ring]
  exact Nat.mod_eq_of_lt hb

theorem ecProjPairEncode_val {w p : ℕ} [NeZero p] (hhi : p ≤ 2 ^ w) (X Y Z X' Y' Z' : ZMod p) :
    ((ecProjPairEncode w (X, Y, Z) (X', Y', Z')).val : ℕ) =
      nest6 (2 ^ w) X.val Y.val Z.val X'.val Y'.val Z'.val := by
  have hpow : 2 ^ (2 * (3 * w)) = 2 ^ (3 * w) * 2 ^ (3 * w) := by rw [two_mul, pow_add]
  have h3 : 2 ^ (3 * w) = 2 ^ w * 2 ^ w * 2 ^ w := by
    rw [show 3 * w = w + w + w by omega, pow_add, pow_add]
  have hb : ((ecProjEncode w (X, Y, Z)).val : ℕ) + 2 ^ (3 * w) * (ecProjEncode w (X', Y', Z')).val <
      2 ^ (2 * (3 * w)) := by
    have hu := (ecProjEncode w (X, Y, Z)).isLt
    have h1 : 2 ^ (3 * w) * ((ecProjEncode w (X', Y', Z')).val + 1) ≤
        2 ^ (3 * w) * 2 ^ (3 * w) := Nat.mul_le_mul_left _ (ecProjEncode w (X', Y', Z')).isLt
    rw [hpow]
    rw [mul_add, mul_one] at h1
    linarith
  show (((ecProjEncode w (X, Y, Z)).val : ℕ) + 2 ^ (3 * w) * (ecProjEncode w (X', Y', Z')).val) %
    2 ^ (2 * (3 * w)) = _
  rw [Nat.mod_eq_of_lt hb, ecProjEncode_val hhi, ecProjEncode_val hhi, h3, nest6]
  ring

theorem localIdx_writeReg_natBits {k : ℕ} (β : BitAssignment n) (r : QRegister k n) (v : ℕ)
    (hv : v < 2 ^ k) : (localIdx r (writeReg β r (natBits k v)) : ℕ) = v := by
  rw [localIdx_writeReg]
  have : (basisBits k).symm (natBits k v) = ⟨v, hv⟩ := by
    rw [Equiv.symm_apply_eq, basisBits_mk_eq_natBits]
  rw [this]

theorem eq_writeReg_of_localIdx {k : ℕ} (r : QRegister k n) (β β' : BitAssignment n)
    (h : ∀ q ∉ Set.range r.wires, β' q = β q) (γ : Fin (2 ^ k)) (hγ : localIdx r β' = γ) :
    β' = writeReg β r (basisBits k γ) := by
  rw [← hγ]
  have : basisBits k (localIdx r β') = fun i ↦ β' (r i) := by
    rw [localIdx, Equiv.apply_symm_apply]
  rw [this, writeReg_eq_of_eqOn β β' r h]

theorem runList_final {w p : ℕ} [NeZero p] (hp : p < 2 ^ w) (a b xQ yQ : ZMod p)
    (σ : Equiv.Perm (Fin (2 ^ (2 * (3 * w)))))
    (hσ : IsECAddProjPerm w a b xQ (projAddFn xQ yQ) σ)
    (rData : QRegister (2 * (3 * w)) n) (rAnc : QRegister (24 * w + 26) n)
    (hdisj : rData.DisjointWires rAnc) {β : BitAssignment n} (hβ : localIdx rAnc β = 0)
    (hvalid : localIdx rData β ∈ ecAddProjValidInputs w a b xQ) :
    runList (ecAddProjSteps xQ yQ rData rAnc) β =
      some (writeReg β rData (basisBits (2 * (3 * w)) (σ (localIdx rData β)))) := by
  obtain ⟨x, y, T, hns, hx, hrep, hidx⟩ := hvalid
  obtain ⟨X, Y, Z⟩ := T
  have hσT := hσ x y hns hx (X, Y, Z) hrep
  have hhi : p ≤ 2 ^ w := hp.le
  have hlt : ∀ z : ZMod p, z.val < 2 ^ w := fun z ↦ (ZMod.val_lt z).trans hp
  have hnest := localIdx_nest6 rData β
  rw [hidx, ecProjPairEncode_val hhi] at hnest
  simp only [ZMod.val_zero] at hnest
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := nest6_inj (hlt X) (hlt Y) (hlt Z) (by positivity)
    (by positivity) (Fin.isLt _) (Fin.isLt _) (Fin.isLt _) (Fin.isLt _) (Fin.isLt _) hnest
  have hbits : ∀ (k : Fin 6) (v : ℕ), (localIdx (dChunk rData k) β : ℕ) = v → v < 2 ^ w →
      ∀ i, β (dChunk rData k i) = natBits w v i := fun k v hk hv ↦
    bits_of_localIdx _ β v hv hk
  have hz : ∀ k : Fin 6, (localIdx (dChunk rData k) β : ℕ) = 0 → ∀ i, β (dChunk rData k i) = 0 :=
    fun k hk i ↦ by
      rw [hbits k 0 hk (Nat.two_pow_pos _) i]; simp [natBits]
  have hrun := runList_prog hp xQ yQ X Y Z rData rAnc hdisj hβ (hbits 0 _ e0.symm (hlt X))
    (hbits 1 _ e1.symm (hlt Y)) (hbits 2 _ e2.symm (hlt Z)) (hz 3 e3.symm)
    (hz 4 e4.symm) (hz 5 e5.symm)
  rw [hrun]
  refine congrArg some (eq_writeReg_of_localIdx rData β _ ?_ _ ?_)
  · intro q hq
    have hq' : ∀ k : Fin 6, q ∉ Set.range (dChunk rData k).wires := fun k hmem ↦
      hq (by obtain ⟨i, rfl⟩ := hmem; exact mem_range_slice rData _ _ _ i)
    rw [writeReg_apply_of_not_mem _ _ _ _ (hq' 5), writeReg_apply_of_not_mem _ _ _ _ (hq' 4),
      writeReg_apply_of_not_mem _ _ _ _ (hq' 3)]
  · rw [hidx, hσT]
    refine Fin.ext ?_
    rw [localIdx_nest6, ecProjPairEncode_val hhi]
    have d03 := chunk_disj rData 0 3 (by decide)
    have d04 := chunk_disj rData 0 4 (by decide)
    have d05 := chunk_disj rData 0 5 (by decide)
    have d13 := chunk_disj rData 1 3 (by decide)
    have d14 := chunk_disj rData 1 4 (by decide)
    have d15 := chunk_disj rData 1 5 (by decide)
    have d23 := chunk_disj rData 2 3 (by decide)
    have d24 := chunk_disj rData 2 4 (by decide)
    have d25 := chunk_disj rData 2 5 (by decide)
    have d34 := chunk_disj rData 3 4 (by decide)
    have d35 := chunk_disj rData 3 5 (by decide)
    have d45 := chunk_disj rData 4 5 (by decide)
    simp only [projAddFn]
    rw [localIdx_writeReg_of_disjoint _ _ _ (QRegister.disjoint_comm.1 d05),
      localIdx_writeReg_of_disjoint _ _ _ (QRegister.disjoint_comm.1 d04),
      localIdx_writeReg_of_disjoint _ _ _ (QRegister.disjoint_comm.1 d03),
      localIdx_writeReg_of_disjoint _ _ _ (QRegister.disjoint_comm.1 d15),
      localIdx_writeReg_of_disjoint _ _ _ (QRegister.disjoint_comm.1 d14),
      localIdx_writeReg_of_disjoint _ _ _ (QRegister.disjoint_comm.1 d13),
      localIdx_writeReg_of_disjoint _ _ _ (QRegister.disjoint_comm.1 d25),
      localIdx_writeReg_of_disjoint _ _ _ (QRegister.disjoint_comm.1 d24),
      localIdx_writeReg_of_disjoint _ _ _ (QRegister.disjoint_comm.1 d23),
      localIdx_writeReg_of_disjoint _ _ _ (QRegister.disjoint_comm.1 d35),
      localIdx_writeReg_of_disjoint _ _ _ (QRegister.disjoint_comm.1 d34),
      localIdx_writeReg_of_disjoint _ _ _ (QRegister.disjoint_comm.1 d45),
      localIdx_writeReg_natBits _ _ _ (hlt _), localIdx_writeReg_natBits _ _ _ (hlt _),
      localIdx_writeReg_natBits _ _ _ (hlt _), e0, e1, e2]

/-!
## Stage C5: AND count
-/

theorem andCount_ecAddProjSteps {w p : ℕ} (xQ yQ : ZMod p) (rData : QRegister (2 * (3 * w)) n)
    (rAnc : QRegister (24 * w + 26) n) :
    ((ecAddProjSteps xQ yQ rData rAnc).map Step.andCount).sum = 44 * (w * w * (5 * w + 1)) := by
  have hS1 : ((setupSteps xQ yQ rData rAnc).map Step.andCount).sum = 0 := by
    simp only [setupSteps, List.map_append, List.sum_append, andCount_copySteps,
      andCount_xorSteps]
  have hS2 : ((setupSteps xQ yQ rData rAnc).map uCount).sum = 0 := by
    simp only [setupSteps, List.map_append, List.sum_append, uCount_copySteps, uCount_xorSteps]
  have hO := andCount_opsSteps (p := p) (ancReg rAnc) (ancA rAnc) (ancC rAnc) (ancCi rAnc)
    (ancF rAnc) (ancG rAnc) ecOps
  have hU := uCount_opsSteps (p := p) (ancReg rAnc) (ancA rAnc) (ancC rAnc) (ancCi rAnc)
    (ancF rAnc) (ancG rAnc) ecOps
  have hCo : ((copyOutSteps rData rAnc).map Step.andCount).sum = 0 := by
    simp only [copyOutSteps, List.map_append, List.sum_append, andCount_copySteps]
  have hC : ((ecC xQ yQ rData rAnc).map Step.andCount).sum = 22 * (w * w * (5 * w + 1)) := by
    rw [ecC, List.map_append, List.sum_append, hS1, hO, ecOps_length]; ring
  have hCu : ((ecC xQ yQ rData rAnc).map uCount).sum = 22 * (w * w * (5 * w + 1)) := by
    rw [ecC, List.map_append, List.sum_append, hS2, hU, ecOps_length]; ring
  rw [ecAddProjSteps, List.map_append, List.sum_append, List.map_append, List.sum_append,
    andCount_inv_list, hC, hCo, hCu]
  ring

end ProjPoly

/-!
# Affine specification vocabulary (unchanged from `QuantumSpecs/EllipticCurve/ECPointAdd.lean`)
-/

/-!
## Curve, Encoding & Valid Inputs
-/

/-- The short Weierstrass curve `y² = x³ + a x + b` over `ZMod p`, in affine coordinates. -/
abbrev ecCurve {p : ℕ} (a b : ZMod p) : WeierstrassCurve.Affine (ZMod p) :=
  ⟨0, 0, 0, a, b⟩

/-- Basis index `(x + 2^w * y) mod 2^(2w)` of the `2 * w`-qubit data register encoding the affine
point `(x, y)`, with `x` and `y` the standard representatives in `[0, p)`. The reduction modulo
`2^(2w)` only makes the definition total: it does nothing when `p ≤ 2^w`. -/
def ecEncode (w : ℕ) {p : ℕ} (x y : ZMod p) : Fin (2 ^ (2 * w)) :=
  ⟨(x.val + 2 ^ w * y.val) % 2 ^ (2 * w), Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- Valid inputs: encodings of the affine points `(x, y)` of `ecCurve a b` with `x ≠ xQ`. -/
def ecAddValidInputs (w : ℕ) {p : ℕ} (a b xQ : ZMod p) : Set (Fin (2 ^ (2 * w))) :=
  {u | ∃ x y : ZMod p, (ecCurve a b).Nonsingular x y ∧ x ≠ xQ ∧ u = ecEncode w x y}

/-- A basis permutation `σ` agrees with addition of the classical point `Q = (xQ, yQ)` on valid
inputs: whenever `(x, y)` is an affine point with `x ≠ xQ` and `(x, y) + Q = (x', y')` in the
Mathlib group law, `σ` maps the encoding of `(x, y)` to the encoding of `(x', y')`. -/
def IsECAddPerm (w : ℕ) {p : ℕ} [Fact p.Prime] (a b xQ yQ : ZMod p)
    (hQ : (ecCurve a b).Nonsingular xQ yQ) (σ : Equiv.Perm (Fin (2 ^ (2 * w)))) : Prop :=
  ∀ (x y : ZMod p) (h : (ecCurve a b).Nonsingular x y), x ≠ xQ →
    ∀ (x' y' : ZMod p) (h' : (ecCurve a b).Nonsingular x' y'),
      Point.some x y h + Point.some xQ yQ hQ = Point.some x' y' h' →
        σ (ecEncode w x y) = ecEncode w x' y'

/-- Every valid input has an affine sum, so `IsECAddPerm` constrains `σ` on every valid input. -/
theorem ecAdd_sum_affine {p : ℕ} [Fact p.Prime] (a b xQ yQ : ZMod p)
    (hQ : (ecCurve a b).Nonsingular xQ yQ)
    (x y : ZMod p) (h : (ecCurve a b).Nonsingular x y) (hx : x ≠ xQ) :
    ∃ (x' y' : ZMod p) (h' : (ecCurve a b).Nonsingular x' y'),
      Point.some x y h + Point.some xQ yQ hQ = Point.some x' y' h' :=
  ⟨_, _, _, Point.add_of_X_ne hx⟩

/-- By default we allow only a single variable. -/
inductive ECPointAdd.Var where | v deriving DecidableEq, Inhabited

theorem ecEncode_injective (w p : ℕ) [NeZero p] (hhi : p ≤ 2 ^ w) :
    Injective fun a : ZMod p × ZMod p ↦ ecEncode w a.1 a.2 := by
  have h2 : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by rw [two_mul, pow_add]
  have hlt : ∀ z : ZMod p, z.val < 2 ^ w := fun z ↦ lt_of_lt_of_le (ZMod.val_lt z) hhi
  have hb : ∀ x y : ZMod p, x.val + 2 ^ w * y.val < 2 ^ (2 * w) := by
    intro x y
    have hx := hlt x
    have h1 : 2 ^ w * (y.val + 1) ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul_left _ (hlt y)
    rw [h2]
    rw [mul_add, mul_one] at h1
    linarith
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  have hv := congrArg Fin.val h
  simp only [ecEncode] at hv
  rw [Nat.mod_eq_of_lt (hb x y), Nat.mod_eq_of_lt (hb x' y')] at hv
  obtain ⟨e1, e2⟩ := pair_inj (hlt x) (hlt x') hv
  rw [ZMod.val_injective p e1, ZMod.val_injective p e2]

/-- For every prime `p ≤ 2^w`, curve and affine point `Q`, a permutation satisfying `IsECAddPerm`
exists: translation by `Q` is injective on the valid inputs. -/
theorem exists_isECAddPerm (w p : ℕ) [Fact p.Prime] (hhi : p ≤ 2 ^ w) (a b xQ yQ : ZMod p)
    (hQ : (ecCurve a b).Nonsingular xQ yQ) :
    ∃ σ, IsECAddPerm w a b xQ yQ hQ σ := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have henc := ecEncode_injective w p hhi
  let ι := {xy : ZMod p × ZMod p // (ecCurve a b).Nonsingular xy.1 xy.2 ∧ xy.1 ≠ xQ}
  have hex : ∀ s : ι, ∃ xy : ZMod p × ZMod p, ∃ h' : (ecCurve a b).Nonsingular xy.1 xy.2,
      Point.some s.1.1 s.1.2 s.2.1 + Point.some xQ yQ hQ = Point.some xy.1 xy.2 h' := fun s ↦ by
    obtain ⟨x', y', h', e⟩ := ecAdd_sum_affine a b xQ yQ hQ _ _ s.2.1 s.2.2
    exact ⟨(x', y'), h', e⟩
  choose g hg using hex
  have hginj : Injective g := by
    intro s s' e
    obtain ⟨h1, e1⟩ := hg s
    obtain ⟨h2, e2⟩ := hg s'
    have e3 : Point.some (g s).1 (g s).2 h1 = Point.some (g s').1 (g s').2 h2 := by
      rw [Point.some.injEq]
      exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
    have e4 := add_right_cancel (e1.trans (e3.trans e2.symm))
    rw [Point.some.injEq] at e4
    exact Subtype.ext (Prod.ext e4.1 e4.2)
  obtain ⟨σ, hσ⟩ := exists_perm_extending (fun s : ι ↦ ecEncode w s.1.1 s.1.2)
    (fun s : ι ↦ ecEncode w (g s).1 (g s).2)
    (fun s s' e ↦ Subtype.ext (henc e)) (fun s s' e ↦ hginj (henc e))
  refine ⟨σ, fun x y h hx x' y' h' hsum ↦ ?_⟩
  obtain ⟨h1, e1⟩ := hg ⟨(x, y), h, hx⟩
  have e2 := hsum.symm.trans e1
  rw [Point.some.injEq] at e2
  have := hσ ⟨(x, y), h, hx⟩
  simp only at this
  rw [this, ← e2.1, ← e2.2]

/-!
# The affine program

Part A: the field algebra. `affAddFn` is the out-of-place map computed by the circuit: the
inversion-free projective mixed addition of `(x, y, 1)` and `(xQ, yQ)`, the Fermat inverse
`Z^(p-2)` of the denominator, and the correction `(cx, cy) * (1 - Z * Z^(p-2))`, which equals the
constant `(cx, cy)` exactly when `Z = 0` and `0` otherwise.
-/

section AffAlg

open WeierstrassCurve.Affine

def affAddFn {p : ℕ} (xQ yQ cx cy : ZMod p) (P : ZMod p × ZMod p) : ZMod p × ZMod p :=
  ((projAddFn xQ yQ (P.1, P.2, 1)).1 * (projAddFn xQ yQ (P.1, P.2, 1)).2.2 ^ (p - 2) +
      cx * (1 - (projAddFn xQ yQ (P.1, P.2, 1)).2.2 * (projAddFn xQ yQ (P.1, P.2, 1)).2.2 ^ (p - 2)),
   (projAddFn xQ yQ (P.1, P.2, 1)).2.1 * (projAddFn xQ yQ (P.1, P.2, 1)).2.2 ^ (p - 2) +
      cy * (1 - (projAddFn xQ yQ (P.1, P.2, 1)).2.2 * (projAddFn xQ yQ (P.1, P.2, 1)).2.2 ^ (p - 2)))

theorem fermat_inv {p : ℕ} [Fact p.Prime] {z : ZMod p} (hz : z ≠ 0) : z * z ^ (p - 2) = 1 := by
  have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  rw [← pow_succ', show p - 2 + 1 = p - 1 by omega]
  exact ZMod.pow_card_sub_one_eq_one hz

theorem affAddFn_of_valid {p : ℕ} [Fact p.Prime] (a b xQ yQ cx cy : ZMod p)
    (hQ : (ecCurve a b).Nonsingular xQ yQ) (x y : ZMod p) (h : (ecCurve a b).Nonsingular x y)
    (hx : x ≠ xQ) (x' y' : ZMod p) (h' : (ecCurve a b).Nonsingular x' y')
    (hadd : Point.some x y h + Point.some xQ yQ hQ = Point.some x' y' h') :
    affAddFn xQ yQ cx cy (x, y) = (x', y') := by
  obtain ⟨hZ, hX, hY⟩ := projAddFn_table a b xQ yQ hQ x y h hx (x, y, 1)
    ⟨one_ne_zero, by simp, by simp⟩ x' y' h' hadd
  have hinv := fermat_inv hZ
  simp only [affAddFn]
  rw [hinv, hX, hY]
  have e1 : ∀ c : ZMod p, c * (projAddFn xQ yQ (x, y, 1)).2.2 *
      (projAddFn xQ yQ (x, y, 1)).2.2 ^ (p - 2) = c := fun c ↦ by
    rw [mul_assoc, hinv, mul_one]
  rw [e1, e1]
  simp

/-- The constant `-(Q + Q)`, written with the doubling slope `(3 xQ² + a) / (2 yQ)`. -/
def dblNeg {p : ℕ} (a xQ yQ : ZMod p) : ZMod p × ZMod p :=
  (((3 * xQ ^ 2 + a) * (2 * yQ)⁻¹) ^ 2 - 2 * xQ,
    ((3 * xQ ^ 2 + a) * (2 * yQ)⁻¹) * (((3 * xQ ^ 2 + a) * (2 * yQ)⁻¹) ^ 2 - 2 * xQ - xQ) + yQ)

/-- If `P + Q = -Q` for affine `P`, then `P = -(Q + Q) = dblNeg`. -/
theorem eq_dblNeg {p : ℕ} [Fact p.Prime] (a b xQ yQ : ZMod p)
    (hQ : (ecCurve a b).Nonsingular xQ yQ) (x y : ZMod p) (h : (ecCurve a b).Nonsingular x y)
    (hP : Point.some x y h + Point.some xQ yQ hQ = -Point.some xQ yQ hQ) :
    (x, y) = dblNeg a xQ yQ := by
  have hPQ : Point.some x y h = -(Point.some xQ yQ hQ + Point.some xQ yQ hQ) := by
    rw [neg_add]
    exact (eq_sub_of_add_eq hP).trans (sub_eq_add_neg _ _)
  by_cases hy : yQ = (ecCurve a b).negY xQ yQ
  · rw [Point.add_self_of_Y_eq hy, neg_zero] at hPQ
    exact absurd hPQ (Point.some_ne_zero h)
  · rw [Point.add_self_of_Y_ne' hy, neg_neg] at hPQ
    simp only [Point.some.injEq] at hPQ
    obtain ⟨e1, e2⟩ := hPQ
    have hsl : (ecCurve a b).slope xQ xQ yQ yQ = (3 * xQ ^ 2 + a) * (2 * yQ)⁻¹ := by
      rw [slope_of_Y_ne rfl hy]
      simp only [negY, div_eq_mul_inv]
      rw [show yQ - (-yQ - 0 * xQ - 0) = 2 * yQ by ring]
      simp
    rw [hsl] at e1 e2
    simp only [dblNeg, Prod.mk.injEq]
    constructor
    · rw [e1]; simp only [addX]; ring
    · rw [e2]; simp only [negAddY, addX]; ring

theorem affAddFn_zero {p : ℕ} (hp : 2 < p) (xQ yQ cx cy xR yR : ZMod p) (hx : xR = xQ) :
    affAddFn xQ yQ cx cy (xR, yR) = (cx, cy) := by
  have : p - 2 ≠ 0 := by omega
  simp [affAddFn, projAddFn, hx, zero_pow this]

/-- The inverse step: from `R = P + Q` the map for `-Q` returns `P`, also when `R = -Q`. -/
theorem affAddFn_back {p : ℕ} [Fact p.Prime] (hp : 2 < p) (a b xQ yQ : ZMod p)
    (hQ : (ecCurve a b).Nonsingular xQ yQ) (x y : ZMod p) (h : (ecCurve a b).Nonsingular x y)
    (xR yR : ZMod p) (hR : (ecCurve a b).Nonsingular xR yR)
    (hadd : Point.some x y h + Point.some xQ yQ hQ = Point.some xR yR hR) :
    affAddFn xQ (-yQ) (dblNeg a xQ yQ).1 (dblNeg a xQ yQ).2 (xR, yR) = (x, y) := by
  have hneg : (ecCurve a b).negY xQ yQ = -yQ := by simp [negY]
  have hQ' : (ecCurve a b).Nonsingular xQ (-yQ) := by
    rw [← hneg]; exact (nonsingular_neg ..).mpr hQ
  have eQ : (Point.some xQ (-yQ) hQ' : (ecCurve a b).Point) = -Point.some xQ yQ hQ := by
    rw [Point.neg_some]; simp only [Point.some.injEq, true_and]; exact hneg.symm
  by_cases hxR : xR = xQ
  · rw [affAddFn_zero hp _ _ _ _ _ _ hxR]
    have hsq : yR ^ 2 = yQ ^ 2 := by
      have e1 := (equation_iff _ _).1 hR.1
      have e2 := (equation_iff _ _).1 hQ.1
      simp only [zero_mul, add_zero] at e1 e2
      rw [hxR] at e1
      rw [e1, e2]
    have hfac : (yR - yQ) * (yR + yQ) = 0 := by linear_combination hsq
    rcases mul_eq_zero.1 hfac with h1 | h1
    · have hRQ : (Point.some xR yR hR : (ecCurve a b).Point) = Point.some xQ yQ hQ := by
        simp only [Point.some.injEq]; exact ⟨hxR, sub_eq_zero.1 h1⟩
      rw [hRQ] at hadd
      exact absurd (add_eq_right.1 hadd) (Point.some_ne_zero h)
    · have hRQ : (Point.some xR yR hR : (ecCurve a b).Point) = -Point.some xQ yQ hQ := by
        rw [Point.neg_some]; simp only [Point.some.injEq]
        exact ⟨hxR, by rw [hneg]; exact eq_neg_of_add_eq_zero_left h1⟩
      rw [hRQ] at hadd
      rw [Prod.mk.eta]
      exact (eq_dblNeg a b xQ yQ hQ x y h hadd).symm
  · have hadd' : Point.some xR yR hR + Point.some xQ (-yQ) hQ' = Point.some x y h := by
      rw [eQ, ← hadd, add_neg_cancel_right]
    exact affAddFn_of_valid a b xQ (-yQ) _ _ hQ' xR yR hR hxR x y h hadd'

end AffAlg

/-!
Part B: the register program in natural-number-indexed form. A register is a natural number, an
operation `(d, a, b)` is `acc d ← acc d + acc a * acc b`.
-/

/-- A multiply-accumulate `acc d ← acc d + acc a * acc b`, with natural-number register names. -/
abbrev NOp : Type := ℕ × ℕ × ℕ

def stepN {p : ℕ} (e : ℕ → ZMod p) (o : NOp) : ℕ → ZMod p :=
  Function.update e o.1 (e o.1 + e o.2.1 * e o.2.2)

def evalN {p : ℕ} (e : ℕ → ZMod p) (L : List NOp) : ℕ → ZMod p := L.foldl stepN e

theorem evalN_append {p : ℕ} (e : ℕ → ZMod p) (L₁ L₂ : List NOp) :
    evalN e (L₁ ++ L₂) = evalN (evalN e L₁) L₂ := List.foldl_append ..

/-- A register that no operation of the list writes is unchanged. -/
theorem evalN_frame {p : ℕ} (e : ℕ → ZMod p) (L : List NOp) (j : ℕ)
    (hj : ∀ o ∈ L, o.1 ≠ j) : evalN e L j = e j := by
  induction L generalizing e with
  | nil => rfl
  | cons o L ih =>
    rw [evalN, List.foldl_cons, ← evalN, ih _ (fun o' h ↦ hj o' (List.mem_cons_of_mem _ h))]
    rw [stepN, Function.update_of_ne (Ne.symm (hj o (List.mem_cons_self ..)))]

/-- The 22 multiply-accumulates of the inversion-free mixed addition (registers: 0 `X`, 1 `Y`,
2 `Z`, 3 `xQ`, 4 `yQ`, 5 `1`, 6 `-1`, 17 `X3`, 20 `Y3`, 21 `Z3`). -/
def ecN : List NOp :=
  [(7, 4, 2), (7, 6, 1), (8, 3, 2), (8, 6, 0), (9, 5, 7), (10, 5, 8), (11, 7, 9), (12, 8, 10),
   (13, 12, 8), (14, 11, 2), (15, 12, 0), (16, 5, 14), (16, 6, 13), (16, 6, 15), (16, 6, 15),
   (17, 8, 16), (18, 5, 15), (18, 6, 16), (19, 13, 1), (20, 7, 18), (20, 6, 19), (21, 13, 2)]

theorem evalN_ecN {p : ℕ} (e : ℕ → ZMod p) (h5 : e 5 = 1) (h6 : e 6 = -1)
    (hz : ∀ j, 7 ≤ j → j ≤ 21 → e j = 0) :
    evalN e ecN 17 = (projAddFn (e 3) (e 4) (e 0, e 1, e 2)).1 ∧
    evalN e ecN 20 = (projAddFn (e 3) (e 4) (e 0, e 1, e 2)).2.1 ∧
    evalN e ecN 21 = (projAddFn (e 3) (e 4) (e 0, e 1, e 2)).2.2 := by
  have h7 := hz 7 (by norm_num) (by norm_num)
  have h8 := hz 8 (by norm_num) (by norm_num)
  have h9 := hz 9 (by norm_num) (by norm_num)
  have h10 := hz 10 (by norm_num) (by norm_num)
  have h11 := hz 11 (by norm_num) (by norm_num)
  have h12 := hz 12 (by norm_num) (by norm_num)
  have h13 := hz 13 (by norm_num) (by norm_num)
  have h14 := hz 14 (by norm_num) (by norm_num)
  have h15 := hz 15 (by norm_num) (by norm_num)
  have h16 := hz 16 (by norm_num) (by norm_num)
  have h17 := hz 17 (by norm_num) (by norm_num)
  have h18 := hz 18 (by norm_num) (by norm_num)
  have h19 := hz 19 (by norm_num) (by norm_num)
  have h20 := hz 20 (by norm_num) (by norm_num)
  have h21 := hz 21 (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp [evalN, ecN, stepN, projAddFn, h5, h6, h7, h8, h9, h10, h11, h12,
      h13, h14, h15, h16, h17, h18, h19, h20, h21]
    ring

/-- Round `k` of right-to-left square-and-multiply: the base lives in register `28 + 3k`, the
accumulator in `29 + 3k`; the next base is `31 + 3k`, the next accumulator `32 + 3k`. -/
def roundN (k : ℕ) (bit : Bool) : List NOp :=
  [(30 + 3 * k, 28 + 3 * k, 5), (31 + 3 * k, 28 + 3 * k, 30 + 3 * k),
   (32 + 3 * k, 29 + 3 * k, if bit then 28 + 3 * k else 5)]

theorem evalN_round {p : ℕ} (e : ℕ → ZMod p) (k : ℕ) (bit : Bool) (h5 : e 5 = 1)
    (h30 : e (30 + 3 * k) = 0) (h31 : e (31 + 3 * k) = 0) (h32 : e (32 + 3 * k) = 0) :
    evalN e (roundN k bit) (31 + 3 * k) = e (28 + 3 * k) * e (28 + 3 * k) ∧
    evalN e (roundN k bit) (32 + 3 * k) = e (29 + 3 * k) * (if bit then e (28 + 3 * k) else 1) ∧
    ∀ j, j ≠ 30 + 3 * k → j ≠ 31 + 3 * k → j ≠ 32 + 3 * k →
      evalN e (roundN k bit) j = e j := by
  refine ⟨?_, ?_, ?_⟩
  · simp [evalN, roundN, stepN, Function.update_apply, h5, h30, h31]
  · have n1 : (5 : ℕ) ≠ 31 + 3 * k := by omega
    have n2 : (5 : ℕ) ≠ 30 + 3 * k := by omega
    cases bit <;> simp [evalN, roundN, stepN, h5, h30, h31, h32, n1, n2]
  · intro j h1 h2 h3
    simp [evalN, roundN, stepN, Function.update_apply, h1, h2, h3]

/-- `k` rounds of right-to-left square-and-multiply on the bits of `E`. -/
def expN (E : ℕ) : ℕ → List NOp
  | 0 => []
  | k + 1 => expN E k ++ roundN k (decide (E / 2 ^ k % 2 = 1))

theorem length_expN (E k : ℕ) : (expN E k).length = 3 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [expN, roundN, ih]; ring

theorem evalN_expN {p : ℕ} (e₀ : ℕ → ZMod p) (E : ℕ) (Z : ZMod p) (h5 : e₀ 5 = 1)
    (h28 : e₀ 28 = Z) (h29 : e₀ 29 = 1) (hz : ∀ j, 30 ≤ j → e₀ j = 0) :
    ∀ k, evalN e₀ (expN E k) (28 + 3 * k) = Z ^ 2 ^ k ∧
      evalN e₀ (expN E k) (29 + 3 * k) = Z ^ (E % 2 ^ k) ∧
      (∀ j, j < 28 → evalN e₀ (expN E k) j = e₀ j) ∧
      (∀ j, 30 + 3 * k ≤ j → evalN e₀ (expN E k) j = 0) := by
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_, fun j _ ↦ rfl, fun j hj ↦ hz j (by omega)⟩
    · simpa [expN, evalN] using h28
    · simp [expN, evalN, h29, Nat.mod_one]
  | succ k ih =>
    obtain ⟨hB, hR, hc, hd⟩ := ih
    set e := evalN e₀ (expN E k) with he
    have h5' : e 5 = 1 := by rw [hc 5 (by norm_num), h5]
    obtain ⟨r1, r2, r3⟩ := evalN_round e k (decide (E / 2 ^ k % 2 = 1)) h5'
      (hd _ (by omega)) (hd _ (by omega)) (hd _ (by omega))
    have hev : evalN e₀ (expN E (k + 1)) = evalN e (roundN k (decide (E / 2 ^ k % 2 = 1))) := by
      rw [expN, evalN_append]
    rw [hev]
    refine ⟨?_, ?_, fun j hj ↦ ?_, fun j hj ↦ ?_⟩
    · rw [show 28 + 3 * (k + 1) = 31 + 3 * k by ring, r1, hB, ← pow_add, ← two_mul, ← pow_succ']
    · rw [show 29 + 3 * (k + 1) = 32 + 3 * k by ring, r2, hR, hB]
      have hm : E % 2 ^ (k + 1) = E % 2 ^ k + 2 ^ k * (E / 2 ^ k % 2) := Nat.mod_pow_succ
      rw [hm]
      by_cases hb : E / 2 ^ k % 2 = 1
      · simp [hb, pow_add]
      · have hb0 : E / 2 ^ k % 2 = 0 := by omega
        simp [hb0]
    · rw [r3 j (by omega) (by omega) (by omega), hc j hj]
    · rw [r3 j (by omega) (by omega) (by omega), hd j (by omega)]

/-!
Part C: the layout of the ancilla register. There are `3 * w + 31` field registers of `w + 1`
wires, then the adder workspace (`rA`, `rC`, `ci`, `f`, `g`), then two `w`-wire output registers.
-/

namespace AffPoly

open ArcsinImpl OnEncodingBridge FieldMulCore ProjPoly

variable {n : ℕ}

/-- Total wires of the field registers. -/
def affBase (w : ℕ) : ℕ := (3 * w + 31) * (w + 1)

/-- Wires of the field registers and the adder workspace (everything but the outputs). -/
def affWork (w : ℕ) : ℕ := affBase w + (w + 1) + w + 3

/-- The number of clean ancilla wires of the affine program. -/
def affAnc (w : ℕ) : ℕ := affWork w + 2 * w

theorem affWork_eq (w : ℕ) : affWork w = affBase w + (w + 1) + w + 3 := rfl

theorem affAnc_eq (w : ℕ) : affAnc w = affWork w + 2 * w := rfl

theorem reg_le {w : ℕ} (j : Fin (3 * w + 31)) : (j : ℕ) * (w + 1) + (w + 1) ≤ affBase w :=
  off_le (j : ℕ) (3 * w + 31) w j.isLt

section Layout

variable {w : ℕ} (rAnc : QRegister (affAnc w) n)

/-- Field register `j`: `w + 1` wires at offset `j * (w + 1)`. -/
def affReg (j : Fin (3 * w + 31)) : QRegister (w + 1) n :=
  rAnc.slice ((j : ℕ) * (w + 1)) (w + 1) (by
    have := reg_le j
    have := affWork_eq w
    have := affAnc_eq w
    omega)

def affA : QRegister (w + 1) n :=
  rAnc.slice (affBase w) (w + 1) (by have := affWork_eq w; have := affAnc_eq w; omega)

def affC : QRegister w n :=
  rAnc.slice (affBase w + (w + 1)) w (by have := affWork_eq w; have := affAnc_eq w; omega)

def affCi : Wire n := rAnc ⟨affBase w + (w + 1) + w, by have := affWork_eq w; have := affAnc_eq w; omega⟩
def affF : Wire n :=
  rAnc ⟨affBase w + (w + 1) + w + 1, by have := affWork_eq w; have := affAnc_eq w; omega⟩
def affG : Wire n :=
  rAnc ⟨affBase w + (w + 1) + w + 2, by have := affWork_eq w; have := affAnc_eq w; omega⟩

/-- The two output registers, at the end of the ancilla register. -/
def affOX : QRegister w n := rAnc.slice (affWork w) w (by have := affAnc_eq w; omega)
def affOY : QRegister w n := rAnc.slice (affWork w + w) w (by have := affAnc_eq w; omega)

theorem aff_frame :
    Frame (affReg rAnc) (affA rAnc) (affC rAnc) (affCi rAnc) (affF rAnc) (affG rAnc) := by
  have wne : ∀ a b : Fin (affAnc w), (a : ℕ) ≠ b → rAnc a ≠ rAnc b :=
    fun a b h hab ↦ h (congrArg Fin.val (rAnc.wires.injective hab))
  have hw : ∀ (q : ℕ) (hq : q < affAnc w) (o l : ℕ) (h : o + l ≤ affAnc w),
      o + l ≤ q → rAnc ⟨q, hq⟩ ∉ Set.range (rAnc.slice o l h).wires :=
    fun q hq o l h hle ↦ apply_not_mem_slice rAnc ⟨q, hq⟩ o l h (Or.inr hle)
  have h1 := affWork_eq w
  have h2 := affAnc_eq w
  refine ⟨fun j j' hne ↦ ?_, fun j ↦ ?_, fun j ↦ ?_, ?_, fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact QRegister.slice_disjoint_of_le rAnc _ _ _ _ _ _ (off_le _ _ w h)
    · exact QRegister.disjoint_comm.1
        (QRegister.slice_disjoint_of_le rAnc _ _ _ _ _ _ (off_le _ _ w h))
  · exact QRegister.slice_disjoint_of_le rAnc _ _ _ _ _ _ (by have := reg_le j; omega)
  · exact QRegister.slice_disjoint_of_le rAnc _ _ _ _ _ _ (by have := reg_le j; omega)
  · exact QRegister.slice_disjoint_of_le rAnc _ _ _ _ _ _ (by omega)
  · exact hw _ (by omega) _ _ _ (by have := reg_le j; omega)
  · exact hw _ (by omega) _ _ _ (by have := reg_le j; omega)
  · exact hw _ (by omega) _ _ _ (by have := reg_le j; omega)
  · exact hw _ (by omega) _ _ _ (by omega)
  · exact hw _ (by omega) _ _ _ (by omega)
  · exact hw _ (by omega) _ _ _ (by omega)
  · exact hw _ (by omega) _ _ _ (by omega)
  · exact hw _ (by omega) _ _ _ (by omega)
  · exact hw _ (by omega) _ _ _ (by omega)
  · exact wne _ _ (by show affBase w + (w + 1) + w ≠ affBase w + (w + 1) + w + 1; omega)
  · exact wne _ _ (by show affBase w + (w + 1) + w ≠ affBase w + (w + 1) + w + 2; omega)
  · exact wne _ _ (by show affBase w + (w + 1) + w + 1 ≠ affBase w + (w + 1) + w + 2; omega)

end Layout

/-!
Part D: the natural-number program, as a register-file program. The registers of `ecN`, `expN`
and `finalN` are natural numbers; `fk` turns them into elements of `Fin (3 * w + 31)`.
-/

section Bridge

variable {p : ℕ}

def fk (w k : ℕ) : Fin (3 * w + 31) := ⟨k % (3 * w + 31), Nat.mod_lt _ (by omega)⟩

theorem fk_val {w k : ℕ} (h : k < 3 * w + 31) : (fk w k : ℕ) = k := Nat.mod_eq_of_lt h

def toOp (w : ℕ) (o : NOp) : Op (3 * w + 31) := (fk w o.1, fk w o.2.1, fk w o.2.2)

def finSt (w : ℕ) (e : ℕ → ZMod p) : Fin (3 * w + 31) → ZMod p := fun j ↦ e j

/-- All register names are in range and pairwise distinct. -/
def NOk (w : ℕ) (o : NOp) : Prop :=
  o.1 < 3 * w + 31 ∧ o.2.1 < 3 * w + 31 ∧ o.2.2 < 3 * w + 31 ∧
    o.1 ≠ o.2.1 ∧ o.1 ≠ o.2.2 ∧ o.2.1 ≠ o.2.2

theorem toOp_ok {w : ℕ} {o : NOp} (h : NOk w o) : OpOK (toOp w o) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun e ↦ ?_, fun e ↦ ?_, fun e ↦ ?_⟩
  · have := congrArg Fin.val e
    simp only [toOp, fk_val h1, fk_val h2] at this
    exact h4 this
  · have := congrArg Fin.val e
    simp only [toOp, fk_val h1, fk_val h3] at this
    exact h5 this
  · have := congrArg Fin.val e
    simp only [toOp, fk_val h2, fk_val h3] at this
    exact h6 this

theorem finSt_update {w : ℕ} (e : ℕ → ZMod p) {k : ℕ} (hk : k < 3 * w + 31) (c : ZMod p) :
    Function.update (finSt w e) (fk w k) c = finSt w (Function.update e k c) := by
  funext j
  by_cases h : j = fk w k
  · subst h
    rw [Function.update_self]
    simp [finSt, fk_val hk]
  · have hj : (j : ℕ) ≠ k := fun hj ↦ h (Fin.ext (by rw [fk_val hk]; exact hj))
    rw [Function.update_of_ne h]
    simp [finSt, Function.update_of_ne hj]

theorem evalOp_finSt {w : ℕ} (e : ℕ → ZMod p) {o : NOp} (h : NOk w o) :
    evalOp (finSt w e) (toOp w o) = finSt w (stepN e o) := by
  obtain ⟨h1, h2, h3, -⟩ := h
  simp only [evalOp, toOp, stepN]
  rw [finSt_update e h1]
  simp [finSt, fk_val h1, fk_val h2, fk_val h3]

theorem evalOps_finSt {w : ℕ} (L : List NOp) : ∀ (e : ℕ → ZMod p), (∀ o ∈ L, NOk w o) →
    evalOps (finSt w e) (L.map (toOp w)) = finSt w (evalN e L) := by
  induction L with
  | nil => intro e _; rfl
  | cons o L ih =>
    intro e h
    rw [List.map_cons]
    show evalOps (evalOp (finSt w e) (toOp w o)) (L.map (toOp w)) = _
    rw [evalOp_finSt e (h o (List.mem_cons_self ..)),
      ih _ (fun o' ho' ↦ h o' (List.mem_cons_of_mem _ ho'))]
    rfl

theorem ecN_ok (w : ℕ) : ∀ o ∈ ecN, NOk w o := by
  intro o ho
  simp only [ecN, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [NOk] <;> omega

theorem ecN_writes : ∀ o ∈ ecN, 7 ≤ o.1 ∧ o.1 ≤ 21 := by decide

theorem roundN_ok {w k : ℕ} (hk : k < w) (bit : Bool) : ∀ o ∈ roundN k bit, NOk w o := by
  intro o ho
  simp only [roundN, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · simp only [NOk]; omega
  · simp only [NOk]; omega
  · cases bit <;> simp [NOk] <;> omega

theorem expN_ok (E w : ℕ) : ∀ k, k ≤ w → ∀ o ∈ expN E k, NOk w o := by
  intro k
  induction k with
  | zero => intro _ o ho; simp [expN] at ho
  | succ k ih =>
    intro hk o ho
    rw [expN, List.mem_append] at ho
    rcases ho with ho | ho
    · exact ih (by omega) o ho
    · exact roundN_ok (by omega) _ o ho

/-- Final correction: `m = Z3 * Zinv`, then `ax = X3 * Zinv + (-cx) * m` and likewise `ay`. -/
def finalN (zi : ℕ) : List NOp :=
  [(26, 21, zi), (22, 17, zi), (22, 24, 26), (23, 20, zi), (23, 25, 26)]

theorem finalN_ok (w : ℕ) : ∀ o ∈ finalN (29 + 3 * w), NOk w o := by
  intro o ho
  simp only [finalN, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp only [NOk] <;> omega

theorem evalN_final {p : ℕ} (e : ℕ → ZMod p) (zi : ℕ) (h1 : zi ≠ 22) (h2 : zi ≠ 23)
    (h3 : zi ≠ 26) (h26 : e 26 = 0) :
    evalN e (finalN zi) 22 = e 22 + e 17 * e zi + e 24 * (e 21 * e zi) ∧
    evalN e (finalN zi) 23 = e 23 + e 20 * e zi + e 25 * (e 21 * e zi) := by
  refine ⟨?_, ?_⟩ <;>
  · simp [evalN, finalN, stepN, Function.update_apply, h1, h2, h3, h26] <;> ring

/-- The constants loaded into the register file: `Z = 1`, `xQ`, `yq`, `1`, `-1`, `cx`, `cy`,
`-cx`, `-cy`, and the initial exponent accumulator `1`. -/
def loadsN (xQ yq cx cy : ZMod p) : List (ℕ × ZMod p) :=
  [(2, 1), (3, xQ), (4, yq), (5, 1), (6, -1), (22, cx), (23, cy), (24, -cx), (25, -cy), (29, 1)]

def applyLoads (e : ℕ → ZMod p) (L : List (ℕ × ZMod p)) : ℕ → ZMod p :=
  L.foldl (fun e dc ↦ Function.update e dc.1 dc.2) e

/-- The register file after the copies of `X`, `Y` and the constant loads. -/
def initN (X Y xQ yq cx cy : ZMod p) : ℕ → ZMod p :=
  applyLoads (Function.update (Function.update (fun _ ↦ 0) 0 X) 1 Y) (loadsN xQ yq cx cy)

theorem initN_zero {X Y xQ yq cx cy : ZMod p} {j : ℕ} (h0 : j ≠ 0) (h1 : j ≠ 1) (h2 : j ≠ 2)
    (h3 : j ≠ 3) (h4 : j ≠ 4) (h5 : j ≠ 5) (h6 : j ≠ 6) (h22 : j ≠ 22) (h23 : j ≠ 23)
    (h24 : j ≠ 24) (h25 : j ≠ 25) (h29 : j ≠ 29) : initN X Y xQ yq cx cy j = 0 := by
  simp [initN, applyLoads, loadsN, Function.update_apply, h0, h1, h2, h3, h4, h5, h6, h22, h23,
    h24, h25, h29]

theorem initN_spec (X Y xQ yq cx cy : ZMod p) :
    initN X Y xQ yq cx cy 0 = X ∧ initN X Y xQ yq cx cy 1 = Y ∧ initN X Y xQ yq cx cy 2 = 1 ∧
    initN X Y xQ yq cx cy 3 = xQ ∧ initN X Y xQ yq cx cy 4 = yq ∧ initN X Y xQ yq cx cy 5 = 1 ∧
    initN X Y xQ yq cx cy 6 = -1 ∧ initN X Y xQ yq cx cy 22 = cx ∧
    initN X Y xQ yq cx cy 23 = cy ∧ initN X Y xQ yq cx cy 24 = -cx ∧
    initN X Y xQ yq cx cy 25 = -cy ∧ initN X Y xQ yq cx cy 29 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp [initN, applyLoads, loadsN, Function.update_apply]

/-- The whole program, as a natural-number straight-line program. -/
def affN (E w : ℕ) : List NOp :=
  ecN ++ [(28, 21, 5)] ++ expN E w ++ finalN (29 + 3 * w)

theorem affN_ok (E w : ℕ) : ∀ o ∈ affN E w, NOk w o := by
  intro o ho
  simp only [affN, List.mem_append, List.mem_singleton] at ho
  rcases ho with ((ho | ho) | ho) | ho
  · exact ecN_ok w o ho
  · subst ho; simp only [NOk]; omega
  · exact expN_ok E w w le_rfl o ho
  · exact finalN_ok w o ho

theorem evalN_total {w : ℕ} (hE : p - 2 < 2 ^ w) (X Y xQ yq cx cy : ZMod p) :
    evalN (initN X Y xQ yq cx cy) (affN (p - 2) w) 22 = (affAddFn xQ yq cx cy (X, Y)).1 ∧
    evalN (initN X Y xQ yq cx cy) (affN (p - 2) w) 23 = (affAddFn xQ yq cx cy (X, Y)).2 := by
  obtain ⟨i0, i1, i2, i3, i4, i5, i6, i22, i23, i24, i25, i29⟩ := initN_spec X Y xQ yq cx cy
  set e0 := initN X Y xQ yq cx cy with he0
  have z0 : ∀ j, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → j ≠ 4 → j ≠ 5 → j ≠ 6 → j ≠ 22 → j ≠ 23 →
      j ≠ 24 → j ≠ 25 → j ≠ 29 → e0 j = 0 := fun j h0 h1 h2 h3 h4 h5 h6 h22 h23 h24 h25 h29 ↦
    initN_zero h0 h1 h2 h3 h4 h5 h6 h22 h23 h24 h25 h29
  obtain ⟨a17, a20, a21⟩ := evalN_ecN e0 i5 i6 (fun j hj1 hj2 ↦ z0 j (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega))
  rw [i3, i4, i0, i1, i2] at a17 a20 a21
  unfold affN
  rw [evalN_append, evalN_append, evalN_append]
  set e1 := evalN e0 ecN with he1
  have f1 : ∀ j, (j < 7 ∨ 21 < j) → e1 j = e0 j := fun j hj ↦
    evalN_frame e0 ecN j (fun o ho ↦ by have := ecN_writes o ho; omega)
  set e2 := evalN e1 [(28, 21, 5)] with he2
  have hM : ∀ j, j ≠ 28 → e2 j = e1 j := fun j hj ↦ by
    simp [he2, evalN, stepN, Function.update_of_ne hj]
  have hM28 : e2 28 = e1 28 + e1 21 * e1 5 := by simp [he2, evalN, stepN]
  have e128 : e1 28 = 0 := by
    rw [f1 28 (by omega)]; exact z0 28 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have e15 : e1 5 = 1 := by rw [f1 5 (by omega), i5]
  have e2_5 : e2 5 = 1 := by rw [hM 5 (by omega), e15]
  have e2_28 : e2 28 = (projAddFn xQ yq (X, Y, 1)).2.2 := by
    rw [hM28, e128, e15, a21, zero_add, mul_one]
  have e2_29 : e2 29 = 1 := by rw [hM 29 (by omega), f1 29 (by omega), i29]
  have e2_hz : ∀ j, 30 ≤ j → e2 j = 0 := fun j hj ↦ by
    rw [hM j (by omega), f1 j (by omega)]
    exact z0 j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨hB, hR, hc, hd⟩ := evalN_expN e2 (p - 2) _ e2_5 e2_28 e2_29 e2_hz w
  set e3 := evalN e2 (expN (p - 2) w) with he3
  have e3_26 : e3 26 = 0 := by
    rw [hc 26 (by omega), hM 26 (by omega), f1 26 (by omega)]
    exact z0 26 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  have e3_lo : ∀ j, 22 ≤ j → j < 28 → e3 j = e0 j := fun j hj1 hj ↦ by
    rw [hc j hj, hM j (by omega), f1 j (by omega)]
  obtain ⟨F22, F23⟩ := evalN_final e3 (29 + 3 * w) (by omega) (by omega) (by omega) e3_26
  rw [F22, F23, hR, Nat.mod_eq_of_lt hE]
  have e3_17 : e3 17 = (projAddFn xQ yq (X, Y, 1)).1 := by
    rw [hc 17 (by omega), hM 17 (by omega)]; exact a17
  have e3_20 : e3 20 = (projAddFn xQ yq (X, Y, 1)).2.1 := by
    rw [hc 20 (by omega), hM 20 (by omega)]; exact a20
  have e3_21 : e3 21 = (projAddFn xQ yq (X, Y, 1)).2.2 := by
    rw [hc 21 (by omega), hM 21 (by omega)]; exact a21
  rw [e3_17, e3_20, e3_21, e3_lo 22 (by omega) (by omega), e3_lo 23 (by omega) (by omega),
    e3_lo 24 (by omega) (by omega), e3_lo 25 (by omega) (by omega), i22, i23, i24, i25]
  simp only [affAddFn]
  constructor <;> ring

end Bridge

/-!
Part E: one Bennett block. Copy `X`, `Y` into registers 0 and 1, load the constants, run the
register program `affN`, XOR registers 22 and 23 into the output registers, and uncompute.
-/

section Block

variable {w p : ℕ}

abbrev AInv (rAnc : QRegister (affAnc w) n) (β : BitAssignment n)
    (st : Fin (3 * w + 31) → ZMod p) : Prop :=
  Inv (affReg rAnc) (affA rAnc) (affC rAnc) (affCi rAnc) (affF rAnc) (affG rAnc) β st

/-- The wires of the field registers and adder workspace. -/
def WorkW (rAnc : QRegister (affAnc w) n) (q : Wire n) : Prop :=
  ∃ j : Fin (affAnc w), (j : ℕ) < affWork w ∧ rAnc j = q

/-- The wires the compute phase touches: the work ancillas and the two input chunks. -/
def PB (rAnc : QRegister (affAnc w) n) (rX rY : QRegister w n) (q : Wire n) : Prop :=
  WorkW rAnc q ∨ q ∈ Set.range rX.wires ∨ q ∈ Set.range rY.wires

variable (rAnc : QRegister (affAnc w) n)

theorem workW_slice (o l : ℕ) (h : o + l ≤ affAnc w) (ho : o + l ≤ affWork w) (i : Fin l) :
    WorkW rAnc (rAnc.slice o l h i) :=
  ⟨⟨o + i, by have := i.isLt; omega⟩, by have := i.isLt; show o + (i : ℕ) < _; omega,
    (QRegister.slice_apply rAnc o l h i).symm⟩

theorem workW_reg (j : Fin (3 * w + 31)) (i : Fin (w + 1)) : WorkW rAnc (affReg rAnc j i) :=
  workW_slice rAnc _ _ _ (by have := reg_le j; have := affWork_eq w; omega) i

theorem workW_opd (j : Fin (3 * w + 31)) (i : Fin w) : WorkW rAnc (opd (affReg rAnc) j i) := by
  simp only [opd, QRegister.slice_apply]
  exact workW_reg rAnc j _

theorem workW_A (i : Fin (w + 1)) : WorkW rAnc (affA rAnc i) :=
  workW_slice rAnc _ _ _ (by have := affWork_eq w; omega) i

theorem workW_C (i : Fin w) : WorkW rAnc (affC rAnc i) :=
  workW_slice rAnc _ _ _ (by have := affWork_eq w; omega) i

theorem workW_ci : WorkW rAnc (affCi rAnc) :=
  ⟨⟨affBase w + (w + 1) + w, by have := affWork_eq w; have := affAnc_eq w; omega⟩,
    by have := affWork_eq w; show affBase w + (w + 1) + w < _; omega, rfl⟩

theorem workW_f : WorkW rAnc (affF rAnc) :=
  ⟨⟨affBase w + (w + 1) + w + 1, by have := affWork_eq w; have := affAnc_eq w; omega⟩,
    by have := affWork_eq w; show affBase w + (w + 1) + w + 1 < _; omega, rfl⟩

theorem workW_g : WorkW rAnc (affG rAnc) :=
  ⟨⟨affBase w + (w + 1) + w + 2, by have := affWork_eq w; have := affAnc_eq w; omega⟩,
    by have := affWork_eq w; show affBase w + (w + 1) + w + 2 < _; omega, rfl⟩

theorem not_PB_slice (rX rY : QRegister w n) (hX : rX.DisjointWires rAnc)
    (hY : rY.DisjointWires rAnc) (o l : ℕ) (h : o + l ≤ affAnc w) (ho : affWork w ≤ o)
    (i : Fin l) : ¬ PB rAnc rX rY (rAnc.slice o l h i) := by
  rw [QRegister.slice_apply]
  rintro (⟨j, hj, hjq⟩ | hq | hq)
  · have := congrArg Fin.val (rAnc.wires.injective hjq)
    change (j : ℕ) = o + i at this
    omega
  · exact not_mem_of_disjoint (QRegister.disjoint_comm.1 hX) _ hq
  · exact not_mem_of_disjoint (QRegister.disjoint_comm.1 hY) _ hq

theorem disj_opd_OX (j : Fin (3 * w + 31)) :
    (opd (affReg rAnc) j).DisjointWires (affOX rAnc) :=
  disj_slice_left (QRegister.slice_disjoint_of_le rAnc _ _ _ _ _ _
    (by have := reg_le j; have := affWork_eq w; omega)) _ _ _

theorem disj_opd_OY (j : Fin (3 * w + 31)) :
    (opd (affReg rAnc) j).DisjointWires (affOY rAnc) :=
  disj_slice_left (QRegister.slice_disjoint_of_le rAnc _ _ _ _ _ _
    (by have := reg_le j; have := affWork_eq w; omega)) _ _ _

theorem disj_OX_OY : (affOX rAnc).DisjointWires (affOY rAnc) :=
  QRegister.slice_disjoint_of_le rAnc _ _ _ _ _ _ le_rfl

theorem inv_init' (β : BitAssignment n)
    (hz : ∀ i : Fin (affAnc w), (i : ℕ) < affWork w → β (rAnc i) = 0) :
    AInv rAnc β (finSt w (fun _ : ℕ ↦ (0 : ZMod p))) := by
  have hwz : ∀ q, WorkW rAnc q → β q = 0 := by
    rintro q ⟨j, hj, rfl⟩
    exact hz j hj
  refine ⟨fun j i ↦ ?_, ⟨fun i ↦ ?_, fun i ↦ ?_, ?_⟩, ?_, ?_⟩
  · rw [hwz _ (workW_reg rAnc j i)]
    simp [natBits, finSt]
  · exact hwz _ (workW_A rAnc i)
  · exact hwz _ (workW_C rAnc i)
  · exact hwz _ (workW_ci rAnc)
  · exact hwz _ (workW_f rAnc)
  · exact hwz _ (workW_g rAnc)

/-- Load the constants `c` into the zero registers `k`. -/
def loadList (rAnc : QRegister (affAnc w) n) : List (ℕ × ZMod p) → List (Step n)
  | [] => []
  | kc :: L =>
    xorSteps none (w + 1) (affReg rAnc (fk w kc.1)) (natBits (w + 1) kc.2.val) ++ loadList rAnc L

theorem runList_loadList [NeZero p] (rAnc : QRegister (affAnc w) n) :
    ∀ (L : List (ℕ × ZMod p)) (e : ℕ → ZMod p) (β : BitAssignment n),
    (∀ kc ∈ L, kc.1 < 3 * w + 31) → (L.map Prod.fst).Nodup → (∀ kc ∈ L, e kc.1 = 0) →
    AInv rAnc β (finSt w e) →
    ∃ β', runList (loadList rAnc L) β = some β' ∧ AInv rAnc β' (finSt w (applyLoads e L))
  | [], e, β, _, _, _, hI => ⟨β, rfl, hI⟩
  | kc :: L, e, β, hb, hnd, hz, hI => by
    obtain ⟨k, c⟩ := kc
    have hk : k < 3 * w + 31 := hb (k, c) (List.mem_cons_self ..)
    have h0 : finSt w e (fk w k) = 0 := by
      show e ((fk w k : Fin _) : ℕ) = 0
      rw [fk_val hk]
      exact hz (k, c) (List.mem_cons_self ..)
    have hrun := runList_load (affReg rAnc) (affA rAnc) (affC rAnc) (affCi rAnc) (affF rAnc)
      (affG rAnc) hI (fk w k) h0 c
    have hI' := Inv_writeReg (affReg rAnc) (affA rAnc) (affC rAnc) (affCi rAnc) (affF rAnc)
      (affG rAnc) (aff_frame rAnc) hI (fk w k) c
    rw [finSt_update e hk c] at hI'
    have hnd' := List.nodup_cons.1 hnd
    obtain ⟨β', h', hI''⟩ := runList_loadList rAnc L (Function.update e k c) _
      (fun kc' h ↦ hb kc' (List.mem_cons_of_mem _ h)) hnd'.2
      (fun kc' h ↦ by
        have hne : kc'.1 ≠ k := fun h' ↦ hnd'.1 (List.mem_map.2 ⟨kc', h, h'⟩)
        rw [Function.update_of_ne hne]
        exact hz kc' (List.mem_cons_of_mem _ h)) hI'
    refine ⟨β', ?_, hI''⟩
    rw [loadList, runList_append, hrun, Option.bind_some]
    exact h'

theorem tameL_loadList {P : Wire n → Prop} (rAnc : QRegister (affAnc w) n)
    (hP : ∀ j i, P (affReg rAnc j i)) : ∀ L : List (ℕ × ZMod p), TameL P (loadList rAnc L)
  | [] => tameL_nil
  | kc :: L =>
    tameL_append.2 ⟨tameL_xorSteps none (fun q h ↦ nomatch h) _ _ _ (fun i ↦ hP _ i),
      tameL_loadList rAnc hP L⟩

/-- Setup: copy `X`, `Y` into registers 0 and 1, then load the constants. -/
def blockSetup (xQ yq cx cy : ZMod p) (rX rY : QRegister w n) (rAnc : QRegister (affAnc w) n) :
    List (Step n) :=
  copySteps w rX (opd (affReg rAnc) (fk w 0)) ++
  (copySteps w rY (opd (affReg rAnc) (fk w 1)) ++ loadList rAnc (loadsN xQ yq cx cy))

/-- The compute phase. -/
def blockC (xQ yq cx cy : ZMod p) (rX rY : QRegister w n) (rAnc : QRegister (affAnc w) n) :
    List (Step n) :=
  blockSetup xQ yq cx cy rX rY rAnc ++
    opsSteps (p := p) (affReg rAnc) (affA rAnc) (affC rAnc) (affCi rAnc) (affF rAnc) (affG rAnc)
      ((affN (p - 2) w).map (toOp w))

/-- XOR registers 22 and 23 into the output registers. -/
def blockOut (p : ℕ) (rAnc : QRegister (affAnc w) n) : List (Step n) :=
  copySteps w (opd (affReg rAnc) (fk w 22)) (affOX rAnc) ++
    copySteps w (opd (affReg rAnc) (fk w 23)) (affOY rAnc)

/-- One block: compute, XOR out, uncompute. -/
def blockSteps (xQ yq cx cy : ZMod p) (rX rY : QRegister w n) (rAnc : QRegister (affAnc w) n) :
    List (Step n) :=
  blockC xQ yq cx cy rX rY rAnc ++
    (blockOut p rAnc ++ (blockC xQ yq cx cy rX rY rAnc).reverse.map Step.inv)

theorem tameL_blockC (xQ yq cx cy : ZMod p) (rX rY : QRegister w n)
    (rAnc : QRegister (affAnc w) n) : TameL (PB rAnc rX rY) (blockC xQ yq cx cy rX rY rAnc) := by
  unfold blockC blockSetup
  refine tameL_append.2 ⟨tameL_append.2 ⟨tameL_copySteps _ _ _ (fun i ↦ Or.inr (Or.inl ⟨i, rfl⟩))
    (fun i ↦ Or.inl (workW_opd rAnc _ i)), tameL_append.2 ⟨tameL_copySteps _ _ _
    (fun i ↦ Or.inr (Or.inr ⟨i, rfl⟩)) (fun i ↦ Or.inl (workW_opd rAnc _ i)),
    tameL_loadList rAnc (fun j i ↦ Or.inl (workW_reg rAnc j i)) _⟩⟩, ?_⟩
  exact tameL_opsSteps (affReg rAnc) (affA rAnc) (affC rAnc) (affCi rAnc) (affF rAnc) (affG rAnc)
    (fun j i ↦ Or.inl (workW_reg rAnc j i)) (fun i ↦ Or.inl (workW_A rAnc i))
    (fun i ↦ Or.inl (workW_C rAnc i)) (Or.inl (workW_ci rAnc)) (Or.inl (workW_f rAnc))
    (Or.inl (workW_g rAnc)) _

theorem runList_block [NeZero p] (hp : p < 2 ^ w) (xQ yq cx cy X Y : ZMod p)
    (rX rY : QRegister w n) (rAnc : QRegister (affAnc w) n)
    (hX : rX.DisjointWires rAnc) (hY : rY.DisjointWires rAnc) {β : BitAssignment n}
    (hz : ∀ i : Fin (affAnc w), (i : ℕ) < affWork w → β (rAnc i) = 0)
    (hbX : ∀ i, β (rX i) = natBits w X.val i) (hbY : ∀ i, β (rY i) = natBits w Y.val i) :
    runList (blockSteps xQ yq cx cy rX rY rAnc) β =
      some (writeReg (writeReg β (affOX rAnc)
        (fun i ↦ β (affOX rAnc i) + natBits w (affAddFn xQ yq cx cy (X, Y)).1.val i))
        (affOY rAnc)
        (fun i ↦ β (affOY rAnc i) + natBits w (affAddFn xQ yq cx cy (X, Y)).2.val i)) := by
  have hlt : ∀ z : ZMod p, z.val < 2 ^ w := fun z ↦ (ZMod.val_lt z).trans hp
  have hE : p - 2 < 2 ^ w := by omega
  have hk0 : 0 < 3 * w + 31 := by omega
  have hk1 : 1 < 3 * w + 31 := by omega
  have hF := aff_frame rAnc
  -- copy X, Y
  have I0 : AInv rAnc β (finSt w (fun _ : ℕ ↦ (0 : ZMod p))) := inv_init' rAnc β hz
  have dX : rX.DisjointWires (affReg rAnc (fk w 0)) := disj_slice_right hX _ _ _
  have dY : rY.DisjointWires (affReg rAnc (fk w 1)) := disj_slice_right hY _ _ _
  have dY0 : rY.DisjointWires (affReg rAnc (fk w 0)) := disj_slice_right hY _ _ _
  have c1 := runList_copyIn (affReg rAnc) (affA rAnc) (affC rAnc) (affCi rAnc) (affF rAnc)
    (affG rAnc) hF I0 (fk w 0) rfl rX dX X (hlt X) hbX
  have I1 := Inv_writeReg (affReg rAnc) (affA rAnc) (affC rAnc) (affCi rAnc) (affF rAnc)
    (affG rAnc) hF I0 (fk w 0) X
  rw [finSt_update _ hk0] at I1
  have c2 := runList_copyIn (affReg rAnc) (affA rAnc) (affC rAnc) (affCi rAnc) (affF rAnc)
    (affG rAnc) hF I1 (fk w 1) (by simp [finSt, fk_val hk1]) rY dY Y (hlt Y)
    (fun i ↦ by
      rw [writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint dY0 i)]
      exact hbY i)
  have I2 := Inv_writeReg (affReg rAnc) (affA rAnc) (affC rAnc) (affCi rAnc) (affF rAnc)
    (affG rAnc) hF I1 (fk w 1) Y
  rw [finSt_update _ hk1] at I2
  -- load constants
  have hmap : (loadsN xQ yq cx cy).map Prod.fst = [2, 3, 4, 5, 6, 22, 23, 24, 25, 29] := rfl
  obtain ⟨β3, hload, I3⟩ := runList_loadList rAnc (loadsN xQ yq cx cy)
    (Function.update (Function.update (fun _ : ℕ ↦ (0 : ZMod p)) 0 X) 1 Y) _
    (fun kc hkc ↦ by
      have : kc.1 ∈ (loadsN xQ yq cx cy).map Prod.fst := List.mem_map.2 ⟨kc, hkc, rfl⟩
      rw [hmap] at this
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      omega)
    (by rw [hmap]; decide)
    (fun kc hkc ↦ by
      have : kc.1 ∈ (loadsN xQ yq cx cy).map Prod.fst := List.mem_map.2 ⟨kc, hkc, rfl⟩
      rw [hmap] at this
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      have h0 : kc.1 ≠ 0 := by omega
      have h1 : kc.1 ≠ 1 := by omega
      simp [Function.update_apply, h0, h1])
    I2
  have I3' : AInv rAnc β3 (finSt w (initN X Y xQ yq cx cy)) := I3
  -- run the program
  obtain ⟨γ, hops, I4⟩ := runList_ops (affReg rAnc) (affA rAnc) (affC rAnc) (affCi rAnc)
    (affF rAnc) (affG rAnc) hF hp ((affN (p - 2) w).map (toOp w))
    (fun o ho ↦ by
      obtain ⟨o', ho', rfl⟩ := List.mem_map.1 ho
      exact toOp_ok (affN_ok _ _ o' ho')) I3'
  rw [evalOps_finSt (w := w) (affN (p - 2) w) _ (affN_ok _ _)] at I4
  have hC : runList (blockC xQ yq cx cy rX rY rAnc) β = some γ := by
    simp only [blockC, blockSetup, runList_append, c1, c2, hload, Option.bind_some, hops]
  have hT := tameL_blockC xQ yq cx cy rX rY rAnc
  have hav : ∀ (o l : ℕ) (h : o + l ≤ affAnc w), affWork w ≤ o →
      ∀ s ∈ blockC xQ yq cx cy rX rY rAnc, ∀ i, s.Avoids (rAnc.slice o l h i) :=
    fun o l h ho s hs i ↦ (hT s hs).avoids (not_PB_slice rAnc rX rY hX hY o l h ho i)
  have hav' : ∀ (o l : ℕ) (h : o + l ≤ affAnc w), affWork w ≤ o →
      ∀ s ∈ (blockC xQ yq cx cy rX rY rAnc).reverse.map Step.inv,
        ∀ i, s.Avoids (rAnc.slice o l h i) := by
    intro o l h ho s hs i
    simp only [List.mem_map, List.mem_reverse] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact Step.avoids_inv (hav o l h ho t ht i)
  have hpX : ∀ i, γ (affOX rAnc i) = β (affOX rAnc i) :=
    fun i ↦ runList_preserve _ (affOX rAnc) (fun s hs i ↦ hav _ _ _ le_rfl s hs i) hC i
  have hpY : ∀ i, γ (affOY rAnc i) = β (affOY rAnc i) :=
    fun i ↦ runList_preserve _ (affOY rAnc)
      (fun s hs i ↦ hav _ _ _ (by have := Nat.le_add_right (affWork w) w; exact this) s hs i) hC i
  -- the two result registers
  have hb : ∀ d : Fin (3 * w + 31), ∀ i, γ (opd (affReg rAnc) d i) =
      natBits w (finSt w (evalN (initN X Y xQ yq cx cy) (affN (p - 2) w)) d).val i :=
    fun d ↦ bits_of_localIdx _ γ _ ((ZMod.val_lt _).trans hp)
      (localIdx_opd (affReg rAnc) hp (fun i ↦ I4.1 d i))
  obtain ⟨hU, hV⟩ := evalN_total (w := w) hE X Y xQ yq cx cy
  have hb22 : ∀ i, γ (opd (affReg rAnc) (fk w 22) i) =
      natBits w (affAddFn xQ yq cx cy (X, Y)).1.val i := fun i ↦ by
    rw [hb]
    have : finSt w (evalN (initN X Y xQ yq cx cy) (affN (p - 2) w)) (fk w 22) =
        (affAddFn xQ yq cx cy (X, Y)).1 := by
      show evalN _ _ ((fk w 22 : Fin _) : ℕ) = _
      rw [fk_val (by omega)]
      exact hU
    rw [this]
  have hb23 : ∀ i, γ (opd (affReg rAnc) (fk w 23) i) =
      natBits w (affAddFn xQ yq cx cy (X, Y)).2.val i := fun i ↦ by
    rw [hb]
    have : finSt w (evalN (initN X Y xQ yq cx cy) (affN (p - 2) w)) (fk w 23) =
        (affAddFn xQ yq cx cy (X, Y)).2 := by
      show evalN _ _ ((fk w 23 : Fin _) : ℕ) = _
      rw [fk_val (by omega)]
      exact hV
    rw [this]
  have hcopy : runList (blockOut p rAnc) γ =
      some (writeReg (writeReg γ (affOX rAnc)
        (fun i ↦ β (affOX rAnc i) + natBits w (affAddFn xQ yq cx cy (X, Y)).1.val i))
        (affOY rAnc)
        (fun i ↦ β (affOY rAnc i) + natBits w (affAddFn xQ yq cx cy (X, Y)).2.val i)) := by
    rw [blockOut, runList_append, runList_copySteps w _ _ (disj_opd_OX rAnc _), Option.bind_some,
      runList_copySteps w _ _ (disj_opd_OY rAnc _)]
    have e1 : (fun i ↦ γ (affOX rAnc i) + γ (opd (affReg rAnc) (fk w 22) i)) =
        fun i ↦ β (affOX rAnc i) + natBits w (affAddFn xQ yq cx cy (X, Y)).1.val i :=
      funext fun i ↦ by rw [hpX i, hb22 i]
    rw [e1]
    refine congrArg some (congrArg (writeReg _ (affOY rAnc)) (funext fun i ↦ ?_))
    rw [writeReg_apply_of_not_mem _ _ _ _
        (not_mem_of_disjoint (QRegister.disjoint_comm.1 (disj_OX_OY rAnc)) i),
      writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint (disj_opd_OX rAnc (fk w 23)) i),
      hpY i, hb23 i]
  have hinv : runList ((blockC xQ yq cx cy rX rY rAnc).reverse.map Step.inv) γ = some β :=
    runList_inv (fun s hs ↦ (hT s hs).noUnxor) hC
  rw [blockSteps, runList_append, hC, Option.bind_some, runList_append, hcopy, Option.bind_some,
    runList_writeReg_of_avoids _ (affOY rAnc) (fun s hs i ↦ hav' _ _ _
      (Nat.le_add_right (affWork w) w) s hs i),
    runList_writeReg_of_avoids _ (affOX rAnc) (fun s hs i ↦ hav' _ _ _ le_rfl s hs i), hinv]
  simp only [Option.map_some]

/-- Pointwise form of `runList_block`. -/
theorem runList_block_pt [NeZero p] (hp : p < 2 ^ w) (xQ yq cx cy X Y : ZMod p)
    (rX rY : QRegister w n) (rAnc : QRegister (affAnc w) n)
    (hX : rX.DisjointWires rAnc) (hY : rY.DisjointWires rAnc) {β : BitAssignment n}
    (hz : ∀ i : Fin (affAnc w), (i : ℕ) < affWork w → β (rAnc i) = 0)
    (hbX : ∀ i, β (rX i) = natBits w X.val i) (hbY : ∀ i, β (rY i) = natBits w Y.val i) :
    ∃ β', runList (blockSteps xQ yq cx cy rX rY rAnc) β = some β' ∧
      (∀ q, q ∉ Set.range (affOX rAnc).wires → q ∉ Set.range (affOY rAnc).wires →
        β' q = β q) ∧
      (∀ i, β' (affOX rAnc i) =
        β (affOX rAnc i) + natBits w (affAddFn xQ yq cx cy (X, Y)).1.val i) ∧
      (∀ i, β' (affOY rAnc i) =
        β (affOY rAnc i) + natBits w (affAddFn xQ yq cx cy (X, Y)).2.val i) := by
  refine ⟨_, runList_block hp xQ yq cx cy X Y rX rY rAnc hX hY hz hbX hbY,
    fun q hqX hqY ↦ ?_, fun i ↦ ?_, fun i ↦ ?_⟩
  · rw [writeReg_apply_of_not_mem _ _ _ _ hqY, writeReg_apply_of_not_mem _ _ _ _ hqX]
  · rw [writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint (disj_OX_OY rAnc) i),
      writeReg_apply_reg]
  · rw [writeReg_apply_reg]

/-- Swap two registers with three CNOT copies. -/
def swapSteps (k : ℕ) (a b : QRegister k n) : List (Step n) :=
  copySteps k a b ++ (copySteps k b a ++ copySteps k a b)

theorem runList_swap {k : ℕ} (a b : QRegister k n) (hab : a.DisjointWires b)
    (β : BitAssignment n) :
    ∃ β', runList (swapSteps k a b) β = some β' ∧
      (∀ q, q ∉ Set.range a.wires → q ∉ Set.range b.wires → β' q = β q) ∧
      (∀ i, β' (a i) = β (b i)) ∧ (∀ i, β' (b i) = β (a i)) := by
  have hba : b.DisjointWires a := QRegister.disjoint_comm.1 hab
  have c1 : ∀ x y : ZMod 2, x + (y + x) = y := by decide
  have c2 : ∀ x y : ZMod 2, (y + x) + y = x := by decide
  rw [swapSteps, runList_append, runList_copySteps k a b hab, Option.bind_some, runList_append,
    runList_copySteps k b a hba, Option.bind_some, runList_copySteps k a b hab]
  obtain ⟨β1, hβ1⟩ : ∃ β1, β1 = writeReg β b (fun i ↦ β (b i) + β (a i)) := ⟨_, rfl⟩
  rw [← hβ1]
  have h1a : ∀ i, β1 (a i) = β (a i) := fun i ↦ by
    rw [hβ1, writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hab i)]
  have h1b : ∀ i, β1 (b i) = β (b i) + β (a i) := fun i ↦ by
    rw [hβ1, writeReg_apply_reg]
  have h1o : ∀ q, q ∉ Set.range b.wires → β1 q = β q := fun q hq ↦ by
    rw [hβ1, writeReg_apply_of_not_mem _ _ _ _ hq]
  obtain ⟨β2, hβ2⟩ : ∃ β2, β2 = writeReg β1 a (fun i ↦ β1 (a i) + β1 (b i)) := ⟨_, rfl⟩
  rw [← hβ2]
  have h2a : ∀ i, β2 (a i) = β (b i) := fun i ↦ by
    simp only [hβ2, writeReg_apply_reg, h1a, h1b, c1]
  have h2b : ∀ i, β2 (b i) = β (b i) + β (a i) := fun i ↦ by
    rw [hβ2, writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hba i), h1b]
  have h2o : ∀ q, q ∉ Set.range a.wires → β2 q = β1 q := fun q hq ↦ by
    rw [hβ2, writeReg_apply_of_not_mem _ _ _ _ hq]
  refine ⟨_, rfl, fun q hqa hqb ↦ ?_, fun i ↦ ?_, fun i ↦ ?_⟩
  · rw [writeReg_apply_of_not_mem _ _ _ _ hqb, h2o q hqa, h1o q hqb]
  · rw [writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hab i), h2a]
  · simp only [writeReg_apply_reg, h2b, h2a, c2]

theorem pair_lt_pow {w x y : ℕ} (hx : x < 2 ^ w) (hy : y < 2 ^ w) : x + 2 ^ w * y < 2 ^ (2 * w) := by
  have h2 : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by rw [two_mul, pow_add]
  have h1 : 2 ^ w * (y + 1) ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul_left _ hy
  rw [h2]
  rw [mul_add, mul_one] at h1
  linarith

theorem localIdx_of_bits {k : ℕ} (r : QRegister k n) (β : BitAssignment n) (v : ℕ)
    (hv : v < 2 ^ k) (h : ∀ i, β (r i) = natBits k v i) : (localIdx r β : ℕ) = v := by
  have : localIdx r β = ⟨v, hv⟩ := by
    rw [localIdx, Equiv.symm_apply_eq, basisBits_mk_eq_natBits]
    funext i
    exact h i
  rw [this]

/-- The data register's `x` chunk. -/
abbrev datX (rData : QRegister (2 * w) n) : QRegister w n := rData.slice 0 w (by omega)

/-- The data register's `y` chunk. -/
abbrev datY (rData : QRegister (2 * w) n) : QRegister w n := rData.slice w w (by omega)

/-- The whole affine program: block with `Q`, swap data and output, block with `-Q`. -/
def affSteps (a xQ yQ : ZMod p) (rData : QRegister (2 * w) n) (rAnc : QRegister (affAnc w) n) :
    List (Step n) :=
  blockSteps xQ yQ (dblNeg a xQ yQ).1 (dblNeg a xQ yQ).2 (datX rData) (datY rData) rAnc ++
    (swapSteps w (datX rData) (affOX rAnc) ++
      (swapSteps w (datY rData) (affOY rAnc) ++
        blockSteps xQ (-yQ) (dblNeg a xQ yQ).1 (dblNeg a xQ yQ).2 (datX rData) (datY rData)
          rAnc))

theorem runList_aff [Fact p.Prime] (hp : p < 2 ^ w) (hp3 : 2 < p) (a b xQ yQ : ZMod p)
    (hQ : (ecCurve a b).Nonsingular xQ yQ)
    (σ : Equiv.Perm (Fin (2 ^ (2 * w)))) (hσ : IsECAddPerm w a b xQ yQ hQ σ)
    (rData : QRegister (2 * w) n) (rAnc : QRegister (affAnc w) n)
    (hdisj : rData.DisjointWires rAnc) {β : BitAssignment n} (hβ : localIdx rAnc β = 0)
    (hvalid : localIdx rData β ∈ ecAddValidInputs w a b xQ) :
    runList (affSteps a xQ yQ rData rAnc) β =
      some (writeReg β rData (basisBits (2 * w) (σ (localIdx rData β)))) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨x, y, hns, hx, hidx⟩ := hvalid
  obtain ⟨x', y', hns', hadd⟩ := ecAdd_sum_affine a b xQ yQ hQ x y hns hx
  have hσT : σ (ecEncode w x y) = ecEncode w x' y' := hσ x y hns hx x' y' hns' hadd
  have hlt : ∀ z : ZMod p, z.val < 2 ^ w := fun z ↦ (ZMod.val_lt z).trans hp
  have hval : (localIdx rData β : ℕ) = x.val + 2 ^ w * y.val := by
    rw [hidx]
    exact Nat.mod_eq_of_lt (pair_lt_pow (hlt x) (hlt y))
  have hsplit := localIdx_val_split rData w w (by omega) β
  rw [hval] at hsplit
  obtain ⟨e0, e1⟩ := pair_inj (hlt x) (Fin.isLt _) hsplit
  have hbX : ∀ i, β (datX rData i) = natBits w x.val i :=
    bits_of_localIdx (datX rData) β x.val (hlt x) e0.symm
  have hbY : ∀ i, β (datY rData i) = natBits w y.val i :=
    bits_of_localIdx (datY rData) β y.val (hlt y) e1.symm
  -- disjointness
  have hX : (datX rData).DisjointWires rAnc := disj_slice_left hdisj _ _ _
  have hY : (datY rData).DisjointWires rAnc := disj_slice_left hdisj _ _ _
  have dXY : (datX rData).DisjointWires (datY rData) :=
    QRegister.slice_disjoint_of_le rData _ _ _ _ _ _ (by omega)
  have dXOX : (datX rData).DisjointWires (affOX rAnc) := disj_slice_right hX _ _ _
  have dXOY : (datX rData).DisjointWires (affOY rAnc) := disj_slice_right hX _ _ _
  have dYOX : (datY rData).DisjointWires (affOX rAnc) := disj_slice_right hY _ _ _
  have dYOY : (datY rData).DisjointWires (affOY rAnc) := disj_slice_right hY _ _ _
  have dOO : (affOX rAnc).DisjointWires (affOY rAnc) := disj_OX_OY rAnc
  -- ancillas are zero
  have hz0 : ∀ j : Fin (affAnc w), β (rAnc j) = 0 := anc_bits_zero rAnc β hβ
  have zX : ∀ i, β (affOX rAnc i) = 0 := fun i ↦ by
    simp only [affOX, QRegister.slice_apply]; exact hz0 _
  have zY : ∀ i, β (affOY rAnc i) = 0 := fun i ↦ by
    simp only [affOY, QRegister.slice_apply]; exact hz0 _
  have hnW : ∀ j : Fin (affAnc w), (j : ℕ) < affWork w →
      rAnc j ∉ Set.range (affOX rAnc).wires ∧ rAnc j ∉ Set.range (affOY rAnc).wires :=
    fun j hj ↦ ⟨apply_not_mem_slice rAnc j _ _ _ (Or.inl hj),
      apply_not_mem_slice rAnc j _ _ _ (Or.inl (by omega))⟩
  -- phase 1
  have hA1 : affAddFn xQ yQ (dblNeg a xQ yQ).1 (dblNeg a xQ yQ).2 (x, y) = (x', y') :=
    affAddFn_of_valid a b xQ yQ _ _ hQ x y hns hx x' y' hns' hadd
  obtain ⟨β1, hr1, p1, o1x, o1y⟩ := runList_block_pt hp xQ yQ (dblNeg a xQ yQ).1
    (dblNeg a xQ yQ).2 x y (datX rData) (datY rData) rAnc hX hY (fun i _ ↦ hz0 i) hbX hbY
  rw [hA1] at o1x o1y
  have o1x' : ∀ i, β1 (affOX rAnc i) = natBits w x'.val i := fun i ↦ by
    simp only [o1x i, zX i, zero_add]
  have o1y' : ∀ i, β1 (affOY rAnc i) = natBits w y'.val i := fun i ↦ by
    simp only [o1y i, zY i, zero_add]
  -- swaps
  obtain ⟨β2, hr2, p2, s2a, s2b⟩ := runList_swap (datX rData) (affOX rAnc) dXOX β1
  obtain ⟨β3, hr3, p3, s3a, s3b⟩ := runList_swap (datY rData) (affOY rAnc) dYOY β2
  have b3X : ∀ i, β3 (datX rData i) = natBits w x'.val i := fun i ↦ by
    rw [p3 _ (not_mem_of_disjoint dXY i) (not_mem_of_disjoint dXOY i), s2a, o1x']
  have b3Y : ∀ i, β3 (datY rData i) = natBits w y'.val i := fun i ↦ by
    rw [s3a, p2 _ (not_mem_of_disjoint (QRegister.disjoint_comm.1 dXOY) i)
      (not_mem_of_disjoint (QRegister.disjoint_comm.1 dOO) i), o1y']
  have b3OX : ∀ i, β3 (affOX rAnc i) = natBits w x.val i := fun i ↦ by
    rw [p3 _ (not_mem_of_disjoint (QRegister.disjoint_comm.1 dYOX) i)
      (not_mem_of_disjoint dOO i), s2b,
      p1 _ (not_mem_of_disjoint dXOX i) (not_mem_of_disjoint dXOY i), hbX]
  have hz3 : ∀ j : Fin (affAnc w), (j : ℕ) < affWork w → β3 (rAnc j) = 0 := fun j hj ↦ by
    obtain ⟨n1, n2⟩ := hnW j hj
    rw [p3 _ (not_mem_of_disjoint (QRegister.disjoint_comm.1 hY) j) n2,
      p2 _ (not_mem_of_disjoint (QRegister.disjoint_comm.1 hX) j) n1, p1 _ n1 n2]
    exact hz0 j
  -- phase 2
  have hback := affAddFn_back hp3 a b xQ yQ hQ x y hns x' y' hns' hadd
  obtain ⟨β4, hr4, p4, o4x, o4y⟩ := runList_block_pt hp xQ (-yQ) (dblNeg a xQ yQ).1
    (dblNeg a xQ yQ).2 x' y' (datX rData) (datY rData) rAnc hX hY hz3 b3X b3Y
  rw [hback] at o4x o4y
  have c3 : ∀ z : ZMod 2, z + z = 0 := by decide
  have b3OY : ∀ i, β3 (affOY rAnc i) = natBits w y.val i := fun i ↦ by
    rw [s3b, p2 _ (not_mem_of_disjoint (QRegister.disjoint_comm.1 dXY) i)
      (not_mem_of_disjoint dYOX i),
      p1 _ (not_mem_of_disjoint dYOX i) (not_mem_of_disjoint dYOY i), hbY]
  have f4x : ∀ i, β4 (affOX rAnc i) = 0 := fun i ↦ by
    rw [o4x i, b3OX i]; exact c3 _
  have f4y : ∀ i, β4 (affOY rAnc i) = 0 := fun i ↦ by
    rw [o4y i, b3OY i]; exact c3 _
  have hother : ∀ q, q ∉ Set.range rData.wires → β4 q = β q := fun q hq ↦ by
    have hqX : q ∉ Set.range (datX rData).wires := fun h ↦ hq (by
      obtain ⟨i, rfl⟩ := h; exact mem_range_slice rData _ _ _ i)
    have hqY : q ∉ Set.range (datY rData).wires := fun h ↦ hq (by
      obtain ⟨i, rfl⟩ := h; exact mem_range_slice rData _ _ _ i)
    by_cases hOX : q ∈ Set.range (affOX rAnc).wires
    · obtain ⟨i, rfl⟩ := hOX
      exact (f4x i).trans (zX i).symm
    by_cases hOY : q ∈ Set.range (affOY rAnc).wires
    · obtain ⟨i, rfl⟩ := hOY
      exact (f4y i).trans (zY i).symm
    rw [p4 q hOX hOY, p3 q hqY hOY, p2 q hqX hOX, p1 q hOX hOY]
  have hrun : runList (affSteps a xQ yQ rData rAnc) β = some β4 := by
    rw [affSteps, runList_append, hr1, Option.bind_some, runList_append, hr2, Option.bind_some,
      runList_append, hr3, Option.bind_some, hr4]
  rw [hrun]
  refine congrArg some (eq_writeReg_of_localIdx rData β β4 hother _ ?_)
  rw [hidx, hσT]
  refine Fin.ext ?_
  have g4X : ∀ i, β4 (datX rData i) = natBits w x'.val i := fun i ↦ by
    rw [p4 _ (not_mem_of_disjoint dXOX i) (not_mem_of_disjoint dXOY i)]; exact b3X i
  have g4Y : ∀ i, β4 (datY rData i) = natBits w y'.val i := fun i ↦ by
    rw [p4 _ (not_mem_of_disjoint dYOX i) (not_mem_of_disjoint dYOY i)]; exact b3Y i
  rw [localIdx_val_split rData w w (by omega) β4,
    localIdx_of_bits (datX rData) β4 x'.val (hlt x') g4X,
    localIdx_of_bits (datY rData) β4 y'.val (hlt y') g4Y]
  exact (Nat.mod_eq_of_lt (pair_lt_pow (hlt x') (hlt y'))).symm

/-!
## AND counts
-/

theorem affN_length (E w : ℕ) : (affN E w).length = 3 * w + 28 := by
  simp only [affN, List.length_append, length_expN, List.length_singleton, finalN, ecN,
    List.length_cons, List.length_nil]
  omega

theorem andCount_loadList (rAnc : QRegister (affAnc w) n) :
    ∀ L : List (ℕ × ZMod p), ((loadList rAnc L).map Step.andCount).sum = 0
  | [] => rfl
  | kc :: L => by
    rw [loadList, List.map_append, List.sum_append, andCount_xorSteps,
      andCount_loadList rAnc L]

theorem uCount_loadList (rAnc : QRegister (affAnc w) n) :
    ∀ L : List (ℕ × ZMod p), ((loadList rAnc L).map uCount).sum = 0
  | [] => rfl
  | kc :: L => by
    rw [loadList, List.map_append, List.sum_append, uCount_xorSteps, uCount_loadList rAnc L]

theorem andCount_blockSteps (xQ yq cx cy : ZMod p) (rX rY : QRegister w n)
    (rAnc : QRegister (affAnc w) n) :
    ((blockSteps xQ yq cx cy rX rY rAnc).map Step.andCount).sum =
      2 * ((3 * w + 28) * (w * w * (5 * w + 1))) := by
  have hS1 : ((blockSetup xQ yq cx cy rX rY rAnc).map Step.andCount).sum = 0 := by
    simp only [blockSetup, List.map_append, List.sum_append, andCount_copySteps,
      andCount_loadList]
  have hS2 : ((blockSetup xQ yq cx cy rX rY rAnc).map uCount).sum = 0 := by
    simp only [blockSetup, List.map_append, List.sum_append, uCount_copySteps, uCount_loadList]
  have hO := andCount_opsSteps (p := p) (affReg rAnc) (affA rAnc) (affC rAnc) (affCi rAnc)
    (affF rAnc) (affG rAnc) ((affN (p - 2) w).map (toOp w))
  have hU := uCount_opsSteps (p := p) (affReg rAnc) (affA rAnc) (affC rAnc) (affCi rAnc)
    (affF rAnc) (affG rAnc) ((affN (p - 2) w).map (toOp w))
  have hlen : ((affN (p - 2) w).map (toOp w)).length = 3 * w + 28 := by
    rw [List.length_map, affN_length]
  have hCo : ((blockOut p rAnc).map Step.andCount).sum = 0 := by
    simp only [blockOut, List.map_append, List.sum_append, andCount_copySteps]
  have hC : ((blockC xQ yq cx cy rX rY rAnc).map Step.andCount).sum =
      (3 * w + 28) * (w * w * (5 * w + 1)) := by
    rw [blockC, List.map_append, List.sum_append, hS1, hO, hlen, zero_add]
  have hCu : ((blockC xQ yq cx cy rX rY rAnc).map uCount).sum =
      (3 * w + 28) * (w * w * (5 * w + 1)) := by
    rw [blockC, List.map_append, List.sum_append, hS2, hU, hlen, zero_add]
  rw [blockSteps, List.map_append, List.sum_append, List.map_append, List.sum_append,
    andCount_inv_list, hC, hCo, hCu]
  ring

theorem andCount_swapSteps (k : ℕ) (a b : QRegister k n) :
    ((swapSteps k a b).map Step.andCount).sum = 0 := by
  simp only [swapSteps, List.map_append, List.sum_append, andCount_copySteps]

theorem andCount_affSteps (a xQ yQ : ZMod p) (rData : QRegister (2 * w) n)
    (rAnc : QRegister (affAnc w) n) :
    ((affSteps a xQ yQ rData rAnc).map Step.andCount).sum =
      4 * ((3 * w + 28) * (w * w * (5 * w + 1))) := by
  rw [affSteps, List.map_append, List.sum_append, List.map_append, List.sum_append,
    List.map_append, List.sum_append, andCount_blockSteps, andCount_blockSteps,
    andCount_swapSteps, andCount_swapSteps]
  ring

end Block

end AffPoly

/-!
## The candidate solution
-/

open ArcsinImpl OnEncodingBridge

/-- Number of clean ancilla qubits `ecAddProgram` uses at bit length `w`. -/
def ecAddAncillas (w : ℕ) : ℕ := AffPoly.affAnc w

/-- Point-addition circuit for the classical point `(xQ, yQ)` on `ecCurve a b` over `ZMod p`, on
`2 * w` data wires `rData` (`w` wires for `x` followed by `w` wires for `y`) and `ecAddAncillas w`
clean ancilla wires `rAnc`. -/
def ecAddProgram {n : ℕ} (w p : ℕ) (a b xQ yQ : ZMod p)
    (rData : QRegister (2 * w) n)
    (rAnc : QRegister (ecAddAncillas w) n) : DynamicCircuit ECPointAdd.Var n :=
  compileList ECPointAdd.Var.v (AffPoly.affSteps a xQ yQ rData rAnc)

/-- Parameterized correctness theorem: for a prime `p > 3` of bit length `w` and an affine point
`(xQ, yQ)` of `ecCurve a b`, there is a basis permutation `σ` that agrees with addition of
`(xQ, yQ)` on all valid inputs, and `ecAddProgram` realizes `σ` on valid inputs as a clean
subroutine across all disjoint register placements. -/
theorem ecAdd_correctness (w p : ℕ) [Fact p.Prime]
    (hp : 3 < p) (hlo : 2 ^ (w - 1) < p) (hhi : p < 2 ^ w)
    (a b xQ yQ : ZMod p) (hQ : (ecCurve a b).Nonsingular xQ yQ) :
    ∃ σ : Equiv.Perm (Fin (2 ^ (2 * w))),
      IsECAddPerm w a b xQ yQ hQ σ ∧
      ∀ {n : ℕ}
        (rData : QRegister (2 * w) n)
        (rAnc : QRegister (ecAddAncillas w) n)
        (hdisj : rData.DisjointWires rAnc),
        RealizesCleanSubroutineOnEncoding rData rAnc hdisj (ecAddValidInputs w a b xQ) σ
          (ecAddProgram w p a b xQ yQ rData rAnc).compile := by
  obtain ⟨σ, hσ⟩ := exists_isECAddPerm w p hhi.le a b xQ yQ hQ
  refine ⟨σ, hσ, fun {n} rData rAnc hdisj ↦ ?_⟩
  obtain ⟨R, hK, hR, -⟩ :=
    exists_lowerKraus_compileList ECPointAdd.Var.v (AffPoly.affSteps a xQ yQ rData rAnc)
  exact realizesCleanSubroutineOnEncoding_of_lowerKraus rData rAnc hdisj _ _ hK
    fun β hβ hvalid ↦
      hR β _ (AffPoly.runList_aff hhi (by omega) a b xQ yQ hQ σ hσ rData rAnc hdisj hβ hvalid)

/-!
## `T`-Count Cost Target (all bit lengths)
-/

/-- Claimed `T` count of `ecAddProgram` at bit length `w`. -/
def ecAddTCost (w : ℕ) : ℕ := 16 * ((3 * w + 28) * (w * w * (5 * w + 1)))

theorem ecAddProgram_count {n : ℕ} (w p : ℕ) (a b xQ yQ : ZMod p)
    (rData : QRegister (2 * w) n) (rAnc : QRegister (ecAddAncillas w) n) :
    (ecAddProgram w p a b xQ yQ rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (ecAddProgram w p a b xQ yQ rData rAnc).count PrimitiveGate.T ≤ ecAddTCost w := by
  refine ⟨count_TOFF_compileList _ _, (count_T_compileList _ _).trans ?_⟩
  have h := AffPoly.andCount_affSteps (n := n) (w := w) a xQ yQ rData rAnc
  calc 4 * ((AffPoly.affSteps a xQ yQ rData rAnc).map Step.andCount).sum
      = 4 * (4 * ((3 * w + 28) * (w * w * (5 * w + 1)))) := by rw [h]
    _ = ecAddTCost w := by unfold ecAddTCost; ring
    _ ≤ ecAddTCost w := le_rfl

/-- For every modulus, curve and classical point, `ecAddProgram` uses no primitive `TOFF` gates and
at most `ecAddTCost w` `T` gates, across all register placements. -/
theorem ecAdd_t_cost (w p : ℕ) (a b xQ yQ : ZMod p) {n : ℕ}
    (rData : QRegister (2 * w) n)
    (rAnc : QRegister (ecAddAncillas w) n) :
    let P := ecAddProgram w p a b xQ yQ rData rAnc
    P.count PrimitiveGate.TOFF = 0 ∧ P.count PrimitiveGate.T ≤ ecAddTCost w :=
  ecAddProgram_count w p a b xQ yQ rData rAnc

/-!
## Spacetime Cost Target (`w = 256`)
-/

/-- Claimed spacetime cost (`T count * qubits`) of `ecAddProgram` at bit length `256`. -/
def ecAddW256ConstCost : ℕ := ecAddTCost 256 * (2 * 256 + ecAddAncillas 256)

theorem ecAddW256ConstCost_eq : ecAddW256ConstCost = 221200913434411008 := by
  norm_num [ecAddW256ConstCost, ecAddTCost, ecAddAncillas, AffPoly.affAnc, AffPoly.affWork,
    AffPoly.affBase]

/-- For every modulus, curve and classical point, `ecAddProgram 256` uses no primitive `TOFF` gates
and has spacetime cost `T count * (2 * 256 + ecAddAncillas 256)` at most `ecAddW256ConstCost`,
across all register placements. -/
theorem ecAdd_w256_const_cost (p : ℕ) (a b xQ yQ : ZMod p) {n : ℕ}
    (rData : QRegister (2 * 256) n)
    (rAnc : QRegister (ecAddAncillas 256) n) :
    let P := ecAddProgram 256 p a b xQ yQ rData rAnc
    P.count PrimitiveGate.TOFF = 0 ∧
      P.count PrimitiveGate.T * (2 * 256 + ecAddAncillas 256) ≤ ecAddW256ConstCost :=
  ⟨(ecAddProgram_count 256 p a b xQ yQ rData rAnc).1,
    Nat.mul_le_mul_right _ (ecAddProgram_count 256 p a b xQ yQ rData rAnc).2⟩

end QuantumComputation.Specs
