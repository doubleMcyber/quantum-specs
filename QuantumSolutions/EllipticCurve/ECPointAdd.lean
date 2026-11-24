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
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Tactic.Linarith
public import QuantumComputation.Circuits.DynamicCircuit
public import QuantumComputation.Circuits.ResourceCounting
public import QuantumComputation.QuantumHoareLogic.CleanAncilla

/-!
# Non-vacuity baseline for the `ecAdd` specification, all sizes (table lookup, exponential cost)

This file restates `QuantumSpecs/EllipticCurve/ECPointAdd.lean` with the holes filled and proves all three frozen
theorems for every bit length, prime, curve and point. It shows the specification can be met. It
is NOT the textbook construction: the program looks the answer up in a classical table.

The program: a table `F` on the `k = 2 * w` data qubits is applied in place with four
unary-iteration lookups (`lookupSteps` of the published `Arcsin` solution) on `k` scratch qubits
and `k` iteration qubits: `E ⊕= F(D)`, `D ⊕= G(E)` (now `D = 0`), `D ⊕= E`, `E ⊕= D`, where `G`
inverts `F` on the valid inputs. Both tables are explicit: `F` is the chord formula for adding `Q`
(`ecAddFwd`) and `G` adds `-Q` (`ecAddBwd`, with the tangent formula when the sum has the
abscissa of `Q`). The program is a compiled definition. The permutation `σ` of the correctness
theorem is the one `exists_isECAddPerm` provides (`Classical.choose`); it appears only in the
proof, where it agrees with `F` on the valid inputs.

Holes: `ecAddAncillas w = 4 * w`, `ecAddTCost w = 16 * 2^(2w)`, and the `w = 256` constant
`16 * 2^512 * 1536` (written `ecAddLookupSpacetime 256`). These are exponential in `w`. A polynomial baseline (affine addition with a
modular inversion) is open.

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

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive ECPointAdd.Var where | v deriving DecidableEq, Inhabited

open ECPointAdd (Var)
open ECPointAdd.Var (v)

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
## Any basis permutation by four table lookups
-/

namespace PermLookup

open Function ArcsinImpl

variable {n k : ℕ}

/-- Lookup table of a permutation: the bits of `σ x`. -/
def permTable (σ : Fin (2 ^ k) → Fin (2 ^ k)) (x : ℕ) : BitAssignment k :=
  if h : x < 2 ^ k then basisBits k (σ ⟨x, h⟩) else 0

theorem permTable_val (σ : Fin (2 ^ k) → Fin (2 ^ k)) (j : Fin (2 ^ k)) :
    permTable σ (j : ℕ) = basisBits k (σ j) := by
  rw [permTable, dite_eq_left j.isLt]

/-- Apply the table `F` in place on `rD`, with scratch `rE` and unary-iteration workspace `rW`:
`E ⊕= F(D)`, `D ⊕= G(E)`, `D ⊕= E`, `E ⊕= D`. Correct on inputs `d` with `G (F d) = d`. -/
def permSteps (F G : Fin (2 ^ k) → Fin (2 ^ k)) (rD rE rW : QRegister k n) : List (Step n) :=
  lookupSteps k rE k none rD rW (permTable F) ++
  lookupSteps k rD k none rE rW (permTable G) ++
  lookupSteps k rD k none rE rW (permTable id) ++
  lookupSteps k rE k none rD rW (permTable id)

theorem bits_localIdx (r : QRegister k n) (β : BitAssignment n) (i : Fin k) :
    basisBits k (localIdx r β) i = β (r i) := by
  rw [localIdx, Equiv.apply_symm_apply]

theorem writeReg_zero_of_zero (β : BitAssignment n) (r : QRegister k n)
    (h : ∀ i, β (r i) = 0) : writeReg β r (fun _ ↦ 0) = β := by
  have : (fun _ : Fin k ↦ (0 : ZMod 2)) = fun i ↦ β (r i) := funext fun i ↦ (h i).symm
  rw [this, writeReg_self]

theorem runList_permSteps (F G : Fin (2 ^ k) → Fin (2 ^ k)) (rD rE rW : QRegister k n)
    (hDE : rD.DisjointWires rE) (hDW : rD.DisjointWires rW) (hEW : rE.DisjointWires rW)
    (β : BitAssignment n) (hE : ∀ i, β (rE i) = 0) (hW : ∀ i, β (rW i) = 0)
    (hGF : G (F (localIdx rD β)) = localIdx rD β) :
    runList (permSteps F G rD rE rW) β =
      some (writeReg β rD (basisBits k (F (localIdx rD β)))) := by
  have hED := QRegister.disjoint_comm.1 hDE
  have hWD := QRegister.disjoint_comm.1 hDW
  have hWE := QRegister.disjoint_comm.1 hEW
  have cn : ∀ w : Wire n, CtrlNe none w := ctrlNe_none
  set b := basisBits k (F (localIdx rD β)) with hb
  -- stage 1: E ⊕= σ(D)
  have s1 : runList (lookupSteps k rE k none rD rW (permTable F)) β = some (writeReg β rE b) := by
    rw [runList_lookupSteps k rE k none rD rW _ hDW hDE hWE (fun i ↦ cn _) (fun i ↦ cn _)
      (fun i ↦ cn _) β hW]
    congr 2
    funext i
    rw [hE i, permTable_val, ctrlVal, one_mul, zero_add]
  set β1 := writeReg β rE b with hβ1
  have hW1 : ∀ i, β1 (rW i) = 0 := fun i ↦ by
    rw [hβ1, writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hWE i), hW i]
  have hE1 : localIdx rE β1 = F (localIdx rD β) := by
    rw [hβ1, localIdx_writeReg, hb, Equiv.symm_apply_apply]
  have hD1 : ∀ i, β1 (rD i) = β (rD i) := fun i ↦ by
    rw [hβ1, writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hDE i)]
  -- stage 2: D ⊕= σ⁻¹(E), so D = 0
  have s2 : runList (lookupSteps k rD k none rE rW (permTable G)) β1 =
      some (writeReg β1 rD (fun _ ↦ 0)) := by
    rw [runList_lookupSteps k rD k none rE rW _ hEW hED hWD (fun i ↦ cn _) (fun i ↦ cn _)
      (fun i ↦ cn _) β1 hW1]
    congr 2
    funext i
    rw [hE1, permTable_val, hGF, bits_localIdx, hD1, ctrlVal, one_mul,
      CharTwo.add_self_eq_zero]
  set β2 := writeReg β1 rD (fun _ ↦ 0) with hβ2
  have hW2 : ∀ i, β2 (rW i) = 0 := fun i ↦ by
    rw [hβ2, writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hWD i), hW1 i]
  have hE2 : localIdx rE β2 = F (localIdx rD β) := by
    rw [hβ2, localIdx_writeReg_of_disjoint _ _ _ hDE, hE1]
  -- stage 3: D ⊕= E, so D = σ(d)
  have s3 : runList (lookupSteps k rD k none rE rW (permTable id)) β2 =
      some (writeReg β2 rD b) := by
    rw [runList_lookupSteps k rD k none rE rW _ hEW hED hWD (fun i ↦ cn _) (fun i ↦ cn _)
      (fun i ↦ cn _) β2 hW2]
    congr 2
    funext i
    rw [hE2, permTable_val, id_eq, hβ2, writeReg_apply_reg, ctrlVal, one_mul, zero_add]
  set β3 := writeReg β2 rD b with hβ3
  have hW3 : ∀ i, β3 (rW i) = 0 := fun i ↦ by
    rw [hβ3, writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hWD i), hW2 i]
  have hD3 : localIdx rD β3 = F (localIdx rD β) := by
    rw [hβ3, localIdx_writeReg, hb, Equiv.symm_apply_apply]
  have hE3 : ∀ i, β3 (rE i) = b i := fun i ↦ by
    rw [hβ3, writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hED i), hβ2,
      writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hED i), hβ1, writeReg_apply_reg]
  -- stage 4: E ⊕= D, so E = 0
  have s4 : runList (lookupSteps k rE k none rD rW (permTable id)) β3 =
      some (writeReg β3 rE (fun _ ↦ 0)) := by
    rw [runList_lookupSteps k rE k none rD rW _ hDW hDE hWE (fun i ↦ cn _) (fun i ↦ cn _)
      (fun i ↦ cn _) β3 hW3]
    congr 2
    funext i
    rw [hD3, permTable_val, id_eq, hE3, ctrlVal, one_mul, hb,
      CharTwo.add_self_eq_zero]
  rw [permSteps, runList_append, runList_append, runList_append, s1, Option.bind_some, s2,
    Option.bind_some, s3, Option.bind_some, s4]
  congr 1
  rw [hβ3, hβ2, writeReg_writeReg, hβ1, writeReg_comm β rE rD hED, writeReg_writeReg]
  refine writeReg_zero_of_zero _ _ fun i ↦ ?_
  rw [writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hED i), hE i]

theorem andCount_permSteps (F G : Fin (2 ^ k) → Fin (2 ^ k)) (rD rE rW : QRegister k n) :
    ((permSteps F G rD rE rW).map Step.andCount).sum ≤ 4 * 2 ^ k := by
  have h := fun (rY rX : QRegister k n) T ↦ andCount_lookupSteps k rY k none rX rW T
  rw [permSteps, List.map_append, List.map_append, List.map_append, List.sum_append,
    List.sum_append, List.sum_append]
  have h1 := h rE rD (permTable F)
  have h2 := h rD rE (permTable G)
  have h3 := h rD rE (permTable id)
  have h4 := h rE rD (permTable id)
  omega

end PermLookup


open PermLookup ArcsinImpl OnEncodingBridge

/-- Number of clean ancilla qubits `ecAddProgram` uses at bit length `w`. -/
def ecAddAncillas (w : ℕ) : ℕ := 2 * w + 2 * w

/-- The permutation the lookup program applies: one satisfying `IsECAddPerm` when the parameters
are valid, the identity otherwise. -/
noncomputable def ecAddSigma (w p : ℕ) (a b xQ yQ : ZMod p) : Equiv.Perm (Fin (2 ^ (2 * w))) :=
  open Classical in
  if h : p.Prime ∧ p ≤ 2 ^ w ∧ (ecCurve a b).Nonsingular xQ yQ then
    haveI : Fact p.Prime := ⟨h.1⟩
    Classical.choose (exists_isECAddPerm w p h.2.1 a b xQ yQ h.2.2)
  else Equiv.refl _

theorem ecAddSigma_spec (w p : ℕ) [Fact p.Prime] (hhi : p ≤ 2 ^ w) (a b xQ yQ : ZMod p)
    (hQ : (ecCurve a b).Nonsingular xQ yQ) :
    IsECAddPerm w a b xQ yQ hQ (ecAddSigma w p a b xQ yQ) := by
  have h : p.Prime ∧ p ≤ 2 ^ w ∧ (ecCurve a b).Nonsingular xQ yQ := ⟨Fact.out, hhi, hQ⟩
  rw [ecAddSigma, dite_eq_left h]
  exact Classical.choose_spec (exists_isECAddPerm w p h.2.1 a b xQ yQ h.2.2)

/-- The field element in the low `w` bits of a basis index. -/
def ecDecX (w p : ℕ) (u : ℕ) : ZMod p := ((u % 2 ^ w : ℕ) : ZMod p)

/-- The field element in the bits above the low `w` bits of a basis index. -/
def ecDecY (w p : ℕ) (u : ℕ) : ZMod p := ((u / 2 ^ w : ℕ) : ZMod p)

/-- Forward table: the chord formula for `(x, y) + (xQ, yQ)` on the decoded index. -/
def ecAddFwd (w p : ℕ) (xQ yQ : ZMod p) (u : Fin (2 ^ (2 * w))) : Fin (2 ^ (2 * w)) :=
  let x := ecDecX w p u
  let y := ecDecY w p u
  let l := (y - yQ) * (x - xQ)⁻¹
  let x' := l ^ 2 - x - xQ
  ecEncode w x' (l * (x - x') - y)

/-- Inverse table: `(x, y) + (xQ, -yQ)` on the decoded index, by the tangent formula when
`x = xQ` and the chord formula otherwise. -/
def ecAddBwd (w p : ℕ) (a xQ yQ : ZMod p) (u : Fin (2 ^ (2 * w))) : Fin (2 ^ (2 * w)) :=
  let x := ecDecX w p u
  let y := ecDecY w p u
  let l := if x = xQ then (3 * x ^ 2 + a) * (y + y)⁻¹ else (y + yQ) * (x - xQ)⁻¹
  let x' := l ^ 2 - x - xQ
  ecEncode w x' (l * (x - x') - y)

theorem ecDec_encode (w p : ℕ) [NeZero p] (hhi : p ≤ 2 ^ w) (x y : ZMod p) :
    ecDecX w p (ecEncode w x y) = x ∧ ecDecY w p (ecEncode w x y) = y := by
  have h2 : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by rw [two_mul, pow_add]
  have hlt : ∀ z : ZMod p, z.val < 2 ^ w := fun z ↦ lt_of_lt_of_le (ZMod.val_lt z) hhi
  have hb : x.val + 2 ^ w * y.val < 2 ^ (2 * w) := by
    have hx := hlt x
    have h1 : 2 ^ w * (y.val + 1) ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul_left _ (hlt y)
    rw [h2]
    rw [mul_add, mul_one] at h1
    linarith
  have hv : (ecEncode w x y).val = x.val + 2 ^ w * y.val := by
    simp only [ecEncode]
    exact Nat.mod_eq_of_lt hb
  constructor
  · rw [ecDecX, hv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hlt x), ZMod.natCast_zmod_val]
  · rw [ecDecY, hv, Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt (hlt x),
      zero_add, ZMod.natCast_zmod_val]

theorem ecAddFwd_spec (w p : ℕ) [Fact p.Prime] (hhi : p ≤ 2 ^ w) (a b xQ yQ : ZMod p)
    (hQ : (ecCurve a b).Nonsingular xQ yQ)
    (x y : ZMod p) (h : (ecCurve a b).Nonsingular x y) (hx : x ≠ xQ)
    (x' y' : ZMod p) (h' : (ecCurve a b).Nonsingular x' y')
    (hsum : Point.some x y h + Point.some xQ yQ hQ = Point.some x' y' h') :
    ecAddFwd w p xQ yQ (ecEncode w x y) = ecEncode w x' y' := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ex, ey⟩ := ecDec_encode w p hhi x y
  rw [Point.add_of_X_ne hx, Point.some.injEq] at hsum
  obtain ⟨e1, e2⟩ := hsum
  simp only [ecAddFwd]
  rw [ex, ey, ← e1, ← e2]
  simp only [addX, addY, negAddY, negY, slope_of_X_ne hx, ecCurve]
  congr 1 <;> ring

theorem ecAddBwd_spec (w p : ℕ) [Fact p.Prime] (hhi : p ≤ 2 ^ w) (a b xQ yQ : ZMod p)
    (hQ : (ecCurve a b).Nonsingular xQ yQ)
    (x y : ZMod p) (h : (ecCurve a b).Nonsingular x y)
    (x' y' : ZMod p) (h' : (ecCurve a b).Nonsingular x' y')
    (hsum : Point.some x y h + Point.some xQ yQ hQ = Point.some x' y' h') :
    ecAddBwd w p a xQ yQ (ecEncode w x' y') = ecEncode w x y := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ex, ey⟩ := ecDec_encode w p hhi x' y'
  have hback : Point.some x' y' h' + -Point.some xQ yQ hQ = Point.some x y h := by
    rw [← hsum, add_neg_cancel_right]
  rw [Point.neg_some] at hback
  have hxy : ¬(x' = xQ ∧ y' = (ecCurve a b).negY xQ ((ecCurve a b).negY xQ yQ)) := by
    intro hc
    rw [Point.add_of_Y_eq hc.1 hc.2] at hback
    simp at hback
  rw [Point.add_some hxy, Point.some.injEq] at hback
  obtain ⟨e1, e2⟩ := hback
  simp only [ecAddBwd]
  rw [ex, ey, ← e1, ← e2]
  by_cases hc : x' = xQ
  · have hy : y' ≠ (ecCurve a b).negY xQ ((ecCurve a b).negY xQ yQ) := fun e ↦ hxy ⟨hc, e⟩
    rw [ite_eq_left hc, slope_of_Y_ne hc hy]
    simp only [addX, addY, negAddY, negY, ecCurve]
    congr 1 <;> ring
  · rw [ite_eq_right hc]
    simp only [addX, addY, negAddY, negY, slope_of_X_ne hc, ecCurve]
    congr 1 <;> ring

/-- The lookup program's steps on disjoint data and ancilla registers: an explicit forward table
and an explicit inverse table. -/
def ecAddSteps {n : ℕ} (w p : ℕ) (a _b xQ yQ : ZMod p)
    (rData : QRegister (2 * w) n) (rAnc : QRegister (2 * w + 2 * w) n) : List (Step n) :=
  permSteps (ecAddFwd w p xQ yQ) (ecAddBwd w p a xQ yQ) rData
    (rAnc.slice 0 (2 * w) (by omega)) (rAnc.slice (2 * w) (2 * w) (by omega))

theorem runList_ecAddSteps {n : ℕ} (w p : ℕ) [Fact p.Prime] (hhi : p ≤ 2 ^ w)
    (a b xQ yQ : ZMod p) (hQ : (ecCurve a b).Nonsingular xQ yQ)
    (rData : QRegister (2 * w) n) (rAnc : QRegister (2 * w + 2 * w) n)
    (hdisj : rData.DisjointWires rAnc) (β : BitAssignment n) (hβ : localIdx rAnc β = 0)
    (hv : localIdx rData β ∈ ecAddValidInputs w a b xQ) :
    runList (ecAddSteps w p a b xQ yQ rData rAnc) β =
      some (writeReg β rData (basisBits (2 * w) (ecAddSigma w p a b xQ yQ (localIdx rData β)))) := by
  have hz := anc_bits_zero rAnc β hβ
  obtain ⟨x, y, h, hx, hu⟩ := hv
  obtain ⟨x', y', h', hsum⟩ := ecAdd_sum_affine a b xQ yQ hQ x y h hx
  have hF : ecAddFwd w p xQ yQ (localIdx rData β) =
      ecAddSigma w p a b xQ yQ (localIdx rData β) := by
    rw [hu, ecAddFwd_spec w p hhi a b xQ yQ hQ x y h hx x' y' h' hsum,
      ecAddSigma_spec w p hhi a b xQ yQ hQ x y h hx x' y' h' hsum]
  have hG : ecAddBwd w p a xQ yQ (ecAddFwd w p xQ yQ (localIdx rData β)) = localIdx rData β := by
    rw [hu, ecAddFwd_spec w p hhi a b xQ yQ hQ x y h hx x' y' h' hsum,
      ecAddBwd_spec w p hhi a b xQ yQ hQ x y h x' y' h' hsum]
  rw [← hF]
  exact runList_permSteps _ _ rData _ _
    (hdisj.compose_right _) (hdisj.compose_right _)
    (QRegister.slice_disjoint_of_le rAnc 0 (2 * w) (2 * w) (2 * w) (by omega) (by omega)
      (by omega))
    β (fun i ↦ hz _) (fun i ↦ hz _) hG

theorem andCount_ecAddSteps {n : ℕ} (w p : ℕ) (a b xQ yQ : ZMod p)
    (rData : QRegister (2 * w) n) (rAnc : QRegister (2 * w + 2 * w) n) :
    ((ecAddSteps w p a b xQ yQ rData rAnc).map Step.andCount).sum ≤ 4 * 2 ^ (2 * w) :=
  andCount_permSteps _ _ _ _ _

/-- Point-addition circuit for the classical point `(xQ, yQ)` on `ecCurve a b` over `ZMod p`, on
`2 * w` data wires `rData` (`w` wires for `x` followed by `w` wires for `y`) and `ecAddAncillas w`
clean ancilla wires `rAnc`. -/
def ecAddProgram {n : ℕ} (w p : ℕ) (a b xQ yQ : ZMod p)
    (rData : QRegister (2 * w) n)
    (rAnc : QRegister (ecAddAncillas w) n) : DynamicCircuit Var n :=
  compileList v (ecAddSteps w p a b xQ yQ rData rAnc)

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
  refine ⟨ecAddSigma w p a b xQ yQ, ecAddSigma_spec w p hhi.le a b xQ yQ hQ,
    fun {n} rData rAnc hdisj ↦ ?_⟩
  obtain ⟨R, hK, hR, -⟩ := exists_lowerKraus_compileList v (ecAddSteps w p a b xQ yQ rData rAnc)
  exact realizesCleanSubroutineOnEncoding_of_lowerKraus rData rAnc hdisj _ _ hK
    fun β hβ hv ↦ hR β _ (runList_ecAddSteps w p hhi.le a b xQ yQ hQ rData rAnc hdisj β hβ hv)

/-!
## `T`-Count Cost Target (all bit lengths)
-/

/-- Claimed `T` count of `ecAddProgram` at bit length `w`. -/
def ecAddTCost (w : ℕ) : ℕ := 16 * 2 ^ (2 * w)

theorem ecAddProgram_count {n : ℕ} (w p : ℕ) (a b xQ yQ : ZMod p)
    (rData : QRegister (2 * w) n) (rAnc : QRegister (ecAddAncillas w) n) :
    (ecAddProgram w p a b xQ yQ rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (ecAddProgram w p a b xQ yQ rData rAnc).count PrimitiveGate.T ≤ 16 * 2 ^ (2 * w) := by
  refine ⟨count_TOFF_compileList _ _, (count_T_compileList _ _).trans ?_⟩
  have h := andCount_ecAddSteps w p a b xQ yQ rData rAnc
  omega

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

/-- Spacetime cost of the lookup program at bit length `w`: `16 * 2^(2w)` `T` gates on `6 * w`
qubits. -/
def ecAddLookupSpacetime (w : ℕ) : ℕ := 16 * 2 ^ (2 * w) * (2 * w + (2 * w + 2 * w))

theorem ecAddProgram_spacetime {n : ℕ} (w p : ℕ) (a b xQ yQ : ZMod p)
    (rData : QRegister (2 * w) n) (rAnc : QRegister (ecAddAncillas w) n) :
    (ecAddProgram w p a b xQ yQ rData rAnc).count PrimitiveGate.T * (2 * w + ecAddAncillas w) ≤
      ecAddLookupSpacetime w :=
  Nat.mul_le_mul_right _ (ecAddProgram_count w p a b xQ yQ rData rAnc).2

/-- Claimed spacetime cost (`T count * qubits`) of `ecAddProgram` at bit length `256`. -/
def ecAddW256ConstCost : ℕ := ecAddLookupSpacetime 256

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
    ecAddProgram_spacetime 256 p a b xQ yQ rData rAnc⟩

end QuantumComputation.Specs
