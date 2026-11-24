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

public import QuantumComputation.Circuits.DynamicCircuit
public import QuantumComputation.Circuits.ResourceCounting
public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import QuantumComputationDiscoveries.Primitives.Arcsin.Solution.EqualTableAdd
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Tactic.Linarith

/-!
# ModExp baseline (non-vacuous)

The frozen `QuantumSpecs/ModularArithmetic/ModExp.lean` with its holes filled by a textbook modular exponentiation on
`ℓ + 5 * b + 6` qubits: for each exponent bit `e_j`, an in-place modular multiplication of the
target by the constant `g^(2^j) mod N`, controlled on `e_j`. Each controlled multiplication is
the multiplier of `QuantumSolutions/ModularArithmetic/ModMulConst.lean` with every modular addition doubly controlled
(the AND of the exponent bit and the data bit is computed into one clean wire) and the swap
replaced by a controlled swap. Correctness is proved for all widths `ℓ` and `b`, every modulus
`1 ≤ N ≤ 2^b` and every base coprime to `N`; the `T` count is at most
`4 * ℓ * (10 * b^2 + 3 * b)`.

Credits: the step-list semantics, `rippleSteps`, `xorSteps`, `cswapSteps` and the compile
lemmas come from `QuantumComputationDiscoveries.Primitives.Arcsin.Solution` (Copyright 2026
Google LLC, Apache-2.0). The `OnEncodingBridge` section, `caddcSteps` and the arithmetic helpers
are copied from an unpublished working file of the prime-field multiplication baseline. The modular
adder and the multiplier are copied from earlier revisions of `QuantumSolutions/ModularArithmetic/ModAdd.lean` and
`QuantumSolutions/ModularArithmetic/ModMulConst.lean`.
-/


@[expose] public section

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

open Operator

/-- Widths, modulus and base: `ℓ`-bit exponent register, `b`-bit target register, classical
modulus `1 ≤ N ≤ 2^b`, classical base `g` coprime to `N`. -/
structure ModExpParams where
  /-- Exponent register bit-width `ℓ`. -/
  ℓ : ℕ
  /-- Target register bit-width `b`. -/
  b : ℕ
  /-- Classical modulus `N`. -/
  N : ℕ
  /-- Classical base `g`. -/
  g : ℕ
  /-- The modulus is positive. -/
  hN : 0 < N
  /-- The modulus fits in `b` bits. -/
  hNb : N ≤ 2 ^ b
  /-- The base is invertible modulo `N`. -/
  hcop : Nat.Coprime g N

/-!
## Residue Encoding and the Exponentiation Permutation
-/

/-- `b`-bit basis indices below `N`, identified with `Fin N`. -/
def ModExpParams.residueEquiv (p : ModExpParams) :
    Fin p.N ≃ {y : Fin (2 ^ p.b) // (y : ℕ) < p.N} where
  toFun i := ⟨⟨i, lt_of_lt_of_le i.isLt p.hNb⟩, i.isLt⟩
  invFun y := ⟨y.1, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Residue map `y ↦ g^e * y mod N` for a classical exponent `e`. -/
def modExpMulFun (p : ModExpParams) (e : ℕ) (y : Fin p.N) : Fin p.N :=
  ⟨p.g ^ e * y % p.N, Nat.mod_lt _ p.hN⟩

theorem modExpMulFun_injective (p : ModExpParams) (e : ℕ) :
    Function.Injective (modExpMulFun p e) := by
  intro x y h
  have h' : p.g ^ e * x ≡ p.g ^ e * y [MOD p.N] := congrArg Fin.val h
  have h'' := Nat.ModEq.cancel_left_div_gcd p.hN h'
  rw [Nat.gcd_comm, Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left e p.hcop), Nat.div_one] at h''
  exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt h'' x.isLt y.isLt)

/-- Basis permutation of the target register for a classical exponent `e`:
`y ↦ g^e * y mod N` on residues `y < N`, fixing every `y ≥ N`. -/
noncomputable def modExpMulPerm (p : ModExpParams) (e : ℕ) : Equiv.Perm (Fin (2 ^ p.b)) :=
  Equiv.Perm.extendDomain
    (Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (modExpMulFun_injective p e)))
    p.residueEquiv

/-- Basis permutation on `Fin (2 ^ (p.ℓ + p.b))` for `|e⟩|y⟩ ↦ |e⟩|g^e * y mod N⟩`, with the
pair `(e, y)` read by `splitBasisEquiv`. Only valid inputs (`y < N`) are constrained by the
correctness theorem. -/
noncomputable def modExpPerm (p : ModExpParams) : Equiv.Perm (Fin (2 ^ (p.ℓ + p.b))) :=
  (splitBasisEquiv p.ℓ p.b).trans
    ((Equiv.prodShear (Equiv.refl _) fun e ↦ modExpMulPerm p e.val).trans
      (splitBasisEquiv p.ℓ p.b).symm)

/-- Valid inputs: any exponent `e`, and the target holds a residue, `y < N`. -/
def modExpValidInputs (p : ModExpParams) : Set (Fin (2 ^ (p.ℓ + p.b))) :=
  {i | ((splitBasisEquiv p.ℓ p.b i).2 : ℕ) < p.N}

/-- On valid inputs, `modExpPerm` is `(e, y) ↦ (e, g^e * y mod N)`. -/
theorem modExpPerm_apply_valid (p : ModExpParams) (e : Fin (2 ^ p.ℓ)) (y : Fin (2 ^ p.b))
    (hy : (y : ℕ) < p.N) :
    splitBasisEquiv p.ℓ p.b (modExpPerm p ((splitBasisEquiv p.ℓ p.b).symm (e, y))) =
      (e, ⟨p.g ^ (e : ℕ) * y % p.N, lt_of_lt_of_le (Nat.mod_lt _ p.hN) p.hNb⟩) := by
  simp only [modExpPerm, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.prodShear_apply,
    Equiv.refl_apply, Prod.mk.injEq, true_and]
  rw [modExpMulPerm, Equiv.Perm.extendDomain_apply_subtype _ p.residueEquiv (b := y) hy]
  rfl

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive ModExp.Var where | v deriving DecidableEq, Inhabited

open ModExp (Var)
open ModExp.Var (v)

namespace ModExpImpl

open Operator Matrix QProg Function ArcsinImpl OnEncodingBridge

variable {n : ℕ}

/-- Little-endian bits of a natural number. -/
def natBits (k d : ℕ) : BitAssignment k := fun i ↦ ((d / 2 ^ (i : ℕ) % 2 : ℕ) : ZMod 2)

theorem basisBits_mk_eq_natBits (k m : ℕ) (hm : m < 2 ^ k) :
    basisBits k ⟨m, hm⟩ = natBits k m :=
  funext fun i ↦ basisBits_mk_apply m hm i

/-- Disjointness facts the ripple adder needs: target `rB`, source `rA`, carries `rC`,
carry-in `ci`. -/
structure AddW {w : ℕ} (rB rA : QRegister (w + 1) n) (rC : QRegister w n) (ci : Wire n) :
    Prop where
  hAB : rA.DisjointWires rB
  hAC : rA.DisjointWires rC
  hBC : rB.DisjointWires rC
  ciA : ci ∉ Set.range rA.wires
  ciB : ci ∉ Set.range rB.wires
  ciC : ci ∉ Set.range rC.wires

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

theorem runList_caddc_lt {w : ℕ} {rB rA : QRegister (w + 1) n}
    {rC : QRegister w n} {ci : Wire n} (hW : AddW rB rA rC ci)
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
theorem runList_caddc {w : ℕ} {rB rA : QRegister (w + 1) n}
    {rC : QRegister w n} {ci : Wire n} (hW : AddW rB rA rC ci)
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


theorem runList_ripple {w : ℕ} {rB rA : QRegister (w + 1) n} {rC : QRegister w n} {ci : Wire n}
    (hW : AddW rB rA rC ci) (β : BitAssignment n) (hC0 : ∀ i, β (rC i) = 0) (hci0 : β ci = 0)
    (u : ℕ) (hu : u < 2 ^ (w + 1)) :
    runList (rippleSteps w rA rB ci rC) (writeReg β rB (natBits (w + 1) u)) =
      some (writeReg β rB (natBits (w + 1) (((localIdx rA β : ℕ) + u) % 2 ^ (w + 1)))) := by
  have hBA : rB.DisjointWires rA := QRegister.disjoint_comm.1 hW.hAB
  have hnCB : ∀ i, rC i ∉ Set.range rB.wires := fun i ↦
    not_mem_of_disjoint (QRegister.disjoint_comm.1 hW.hBC) i
  have hidxB : (localIdx rB (writeReg β rB (natBits (w + 1) u)) : ℕ) = u := by
    rw [localIdx_writeReg, ← basisBits_mk_eq_natBits _ _ hu]
    simp
  have hidxA : localIdx rA (writeReg β rB (natBits (w + 1) u)) = localIdx rA β :=
    localIdx_writeReg_of_disjoint _ _ _ hBA _
  have hC : ∀ i, writeReg β rB (natBits (w + 1) u) (rC i) = 0 := fun i ↦ by
    rw [writeReg_apply_of_not_mem _ _ _ _ (hnCB i)]; exact hC0 i
  rw [runList_rippleSteps w rA rB ci rC hW.hAB hW.hAC hW.hBC hW.ciA hW.ciB hW.ciC _ hC,
    basisBits_mk_eq_natBits, hidxA, hidxB, writeReg_apply_of_not_mem _ _ _ _ hW.ciB, hci0,
    ZMod.val_zero, add_zero, writeReg_writeReg]

theorem noUnxor_rippleSteps (k : ℕ) (rA rB : QRegister (k + 1) n) (ci : Wire n)
    (rC : QRegister k n) : ∀ st ∈ rippleSteps k rA rB ci rC, st.NoUnxor := by
  induction k generalizing ci with
  | zero => simp [rippleSteps, Step.NoUnxor]
  | succ k ih =>
    intro st hst
    rw [rippleSteps] at hst
    simp only [List.cons_append, List.mem_cons, List.mem_append] at hst
    rcases hst with rfl | rfl | rfl | rfl | (hst | rfl | rfl | rfl | rfl | hst)
    all_goals first
      | trivial
      | exact ih _ _ _ _ st hst
      | exact ih (regTail rA) (regTail rB) (rC 0) (regTail rC) st hst
      | (simp at hst; done)
      | (simp at hst; exact ih _ _ _ _ st hst)

theorem andCount_inv_rippleSteps (k : ℕ) (rA rB : QRegister (k + 1) n) (ci : Wire n)
    (rC : QRegister k n) :
    ((rippleSteps k rA rB ci rC).map (fun s ↦ s.inv.andCount)).sum = k := by
  induction k generalizing ci with
  | zero => rfl
  | succ k ih =>
    rw [rippleSteps, List.map_append, List.map_append, List.sum_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Step.inv, Step.andCount]
      <;> omega

theorem andCount_ripple_inv (k : ℕ) (rA rB : QRegister (k + 1) n) (ci : Wire n)
    (rC : QRegister k n) :
    ((((rippleSteps k rA rB ci rC).reverse.map Step.inv)).map Step.andCount).sum = k := by
  rw [List.map_map, List.map_reverse, List.sum_reverse]
  exact andCount_inv_rippleSteps k rA rB ci rC

/-- The arithmetic of the modular addition, with `A = 2^b`, in the form of the successive values
`v1, ..., v5` of the `(b + 1)`-bit target and the flag bits `fb`, `hb`. -/
theorem modAddQ_arith (A N x y v1 v2 fb v3 v4 hb v5 : ℕ) (hNA : N ≤ A) (hx : x < N) (hy : y < N)
    (h1 : v1 = (x + y) % (2 * A))
    (h2 : v2 = (v1 + (2 * A - N)) % (2 * A))
    (hfb : fb = v2 / A % 2)
    (h3 : v3 = (v2 + fb * N) % (2 * A))
    (h4 : v4 = (v3 + (2 * A - x)) % (2 * A))
    (hhb : hb = v4 / A % 2)
    (h5 : v5 = (x + v4) % (2 * A)) :
    (fb + hb + 1) % 2 = 0 ∧ v5 = (x + y) % N := by
  by_cases hlt : x + y < N
  · have e1 : v1 = x + y := h1.trans (mod_of_eq_lt (by omega) (by omega))
    have e2 : v2 = x + y + (2 * A - N) := h2.trans (mod_of_eq_lt (by omega) (by omega))
    have e3 : fb = 1 := hfb.trans (div_mod_two_one (by omega) (by omega))
    subst e3
    have e4 : v3 = x + y := h3.trans (mod_of_eq_add_lt (by omega) (by omega))
    have e5 : v4 = y := h4.trans (mod_of_eq_add_lt (by omega) (by omega))
    have e6 : hb = 0 := hhb.trans (div_mod_two_zero (by omega))
    have e7 : v5 = x + y := h5.trans (mod_of_eq_lt (by omega) (by omega))
    refine ⟨by omega, ?_⟩
    rw [e7, Nat.mod_eq_of_lt hlt]
  · have hm : (x + y) % N = x + y - N := by
      rw [Nat.mod_eq_sub_mod (by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    have e1 : v1 = x + y := h1.trans (mod_of_eq_lt (by omega) (by omega))
    have e2 : v2 = x + y - N := h2.trans (mod_of_eq_add_lt (by omega) (by omega))
    have e3 : fb = 0 := hfb.trans (div_mod_two_zero (by omega))
    subst e3
    have e4 : v3 = x + y - N := h3.trans (mod_of_eq_lt (by omega) (by omega))
    have e5 : v4 = y + (2 * A - N) := h4.trans (mod_of_eq_lt (by omega) (by omega))
    have e6 : hb = 1 := hhb.trans (div_mod_two_one (by omega) (by omega))
    have e7 : v5 = x + y - N := h5.trans (mod_of_eq_add_lt (by omega) (by omega))
    refine ⟨by omega, ?_⟩
    rw [e7, hm]

/-- Disjointness facts for the quantum modular adder: source `rX`, target `rY` (each `b + 1`
wires, the top wire an ancilla), constant register `rK`, carries `rC`, carry-in `ci`, flag `f`. -/
structure Lay {b : ℕ} (rX rY rK : QRegister (b + 1) n) (rC : QRegister b n) (ci f : Wire n) :
    Prop where
  hKY : rK.DisjointWires rY
  hKC : rK.DisjointWires rC
  hYC : rY.DisjointWires rC
  hXY : rX.DisjointWires rY
  hXC : rX.DisjointWires rC
  ciK : ci ∉ Set.range rK.wires
  ciY : ci ∉ Set.range rY.wires
  ciC : ci ∉ Set.range rC.wires
  ciX : ci ∉ Set.range rX.wires
  fK : f ∉ Set.range rK.wires
  fY : f ∉ Set.range rY.wires
  fC : f ∉ Set.range rC.wires
  fX : f ∉ Set.range rX.wires
  cif : ci ≠ f

theorem Lay.addK {b : ℕ} {rX rY rK : QRegister (b + 1) n} {rC : QRegister b n} {ci f : Wire n}
    (hL : Lay rX rY rK rC ci f) : AddW rY rK rC ci :=
  ⟨hL.hKY, hL.hKC, hL.hYC, hL.ciK, hL.ciY, hL.ciC⟩

theorem Lay.addX {b : ℕ} {rX rY rK : QRegister (b + 1) n} {rC : QRegister b n} {ci f : Wire n}
    (hL : Lay rX rY rK rC ci f) : AddW rY rX rC ci :=
  ⟨hL.hXY, hL.hXC, hL.hYC, hL.ciX, hL.ciY, hL.ciC⟩

/-- `rY ← (rX + rY) mod N` for `rX, rY < N ≤ 2^b`: add, subtract `N`, add `N` back on underflow
(flag `f` = top bit), then clear `f` by comparing the result with `rX` (subtract `rX`, copy the top
bit, add `rX` back). -/
def modAddQSteps (b N : ℕ) (rX rY rK : QRegister (b + 1) n) (rC : QRegister b n) (ci f : Wire n) :
    List (Step n) :=
  rippleSteps b rX rY ci rC ++
  caddcSteps b rY rK rC ci none (2 ^ (b + 1) - N) ++
  [Step.cnot (rY (Fin.last b)) f] ++
  caddcSteps b rY rK rC ci (some f) N ++
  (rippleSteps b rX rY ci rC).reverse.map Step.inv ++
  [Step.cnot (rY (Fin.last b)) f, Step.x f] ++
  rippleSteps b rX rY ci rC

theorem runList_modAddQ {b N : ℕ} {rX rY rK : QRegister (b + 1) n} {rC : QRegister b n}
    {ci f : Wire n} (hL : Lay rX rY rK rC ci f) (hNb : N ≤ 2 ^ b)
    (β : BitAssignment n) (hclean : Clean rK rC ci β) (hf : β f = 0)
    (x y : ℕ) (hX : (localIdx rX β : ℕ) = x) (hx : x < N) (hy : y < N) :
    runList (modAddQSteps b N rX rY rK rC ci f) (writeReg β rY (natBits (b + 1) y)) =
      some (writeReg β rY (natBits (b + 1) ((x + y) % N))) := by
  have hWK := hL.addK
  have hWX := hL.addX
  have hKf : ∀ i, rK i ≠ f := fun i h ↦ hL.fK ⟨i, h⟩
  have hCf : ∀ i, rC i ≠ f := fun i h ↦ hL.fC ⟨i, h⟩
  have hcl : ∀ a : ZMod 2, Clean rK rC ci (update β f a) := fun a ↦
    ⟨fun i ↦ by rw [update_of_ne (hKf i)]; exact hclean.1 i,
     fun i ↦ by rw [update_of_ne (hCf i)]; exact hclean.2.1 i,
     by rw [update_of_ne hL.cif]; exact hclean.2.2⟩
  have K : ∀ (c : Option (Wire n)) (_ : ∀ i, CtrlNe c (rK i)) (_ : ∀ i, CtrlNe c (rY i))
      (_ : ∀ i, CtrlNe c (rC i)) (_ : CtrlNe c ci) (d : ℕ) (a : ZMod 2) (u : ℕ)
      (_ : u < 2 ^ (b + 1)),
      runList (caddcSteps b rY rK rC ci c d) (writeReg (update β f a) rY (natBits (b + 1) u)) =
        some (writeReg (update β f a) rY (natBits (b + 1)
          ((u + (ctrlVal c (update β f a)).val * d) % 2 ^ (b + 1)))) :=
    fun c hcA hcB hcC hci d a u hu ↦
      runList_caddc hWK c hcA hcB hcC hci d (update β f a) (hcl a) u hu
  have hXa : ∀ a : ZMod 2, (localIdx rX (update β f a) : ℕ) = x := fun a ↦ by
    rw [localIdx_update_of_not_mem _ _ hL.fX, hX]
  have R : ∀ (a : ZMod 2) (u : ℕ) (_ : u < 2 ^ (b + 1)),
      runList (rippleSteps b rX rY ci rC) (writeReg (update β f a) rY (natBits (b + 1) u)) =
        some (writeReg (update β f a) rY (natBits (b + 1) ((x + u) % 2 ^ (b + 1)))) :=
    fun a u hu ↦ by
      rw [runList_ripple hWX (update β f a) (hcl a).2.1 (hcl a).2.2 u hu, hXa a]
  -- the controls
  have cF : (∀ i, CtrlNe (some f) (rK i)) ∧ (∀ i, CtrlNe (some f) (rY i)) ∧
      (∀ i, CtrlNe (some f) (rC i)) ∧ CtrlNe (some f) ci :=
    ⟨fun i ↦ CtrlNe.some (fun h ↦ hL.fK ⟨i, h.symm⟩), fun i ↦ CtrlNe.some (fun h ↦ hL.fY ⟨i, h.symm⟩),
      fun i ↦ CtrlNe.some (fun h ↦ hL.fC ⟨i, h.symm⟩), CtrlNe.some hL.cif.symm⟩
  have cN : (∀ i, CtrlNe none (rK i)) ∧ (∀ i, CtrlNe none (rY i)) ∧
      (∀ i, CtrlNe none (rC i)) ∧ CtrlNe none ci :=
    ⟨fun i ↦ ctrlNe_none _, fun i ↦ ctrlNe_none _, fun i ↦ ctrlNe_none _, ctrlNe_none _⟩
  have hcvF : ∀ a : ZMod 2, ctrlVal (some f) (update β f a) = a := fun a ↦ update_self _ _ _
  have hcvN : ∀ a : ZMod 2, ctrlVal none (update β f a) = 1 := fun a ↦ rfl
  have h1v : (1 : ZMod 2).val = 1 := rfl
  -- flag helpers
  have hset : ∀ (a x : ZMod 2) (u : ℕ), update (writeReg (update β f a) rY (natBits (b + 1) u)) f x =
      writeReg (update β f x) rY (natBits (b + 1) u) := fun a x u ↦ by
    rw [← writeReg_update_of_not_mem _ _ _ hL.fY, update_idem]
  have hgetf : ∀ (a : ZMod 2) (γ : BitAssignment (b + 1)), writeReg (update β f a) rY γ f = a :=
    fun a γ ↦ by rw [writeReg_apply_of_not_mem _ _ _ _ hL.fY, update_self]
  have hne : rY (Fin.last b) ≠ f := fun h ↦ hL.fY ⟨Fin.last b, h⟩
  have hrunC : ∀ S : BitAssignment n, Step.run (Step.cnot (rY (Fin.last b)) f) S =
      some (update S f (S f + S (rY (Fin.last b)))) := fun S ↦ if_pos hne
  have hrunX : ∀ S : BitAssignment n, Step.run (Step.x f) S = some (update S f (S f + 1)) :=
    fun S ↦ rfl
  -- numbers
  obtain ⟨A, hA⟩ : ∃ A, A = 2 ^ b := ⟨_, rfl⟩
  have hA2 : 2 ^ (b + 1) = 2 * A := by rw [hA]; ring
  have hNA : N ≤ A := by rw [hA]; exact hNb
  have hbit : ∀ u : ℕ, natBits (b + 1) u (Fin.last b) = (((u / A % 2 : ℕ)) : ZMod 2) := fun u ↦ by
    simp only [natBits, Fin.val_last, hA]
  have hMpos : 0 < 2 ^ (b + 1) := by positivity
  have hlt : ∀ z : ℕ, z % 2 ^ (b + 1) < 2 ^ (b + 1) := fun z ↦ Nat.mod_lt _ hMpos
  obtain ⟨v1, hv1⟩ : ∃ v1, v1 = (x + y) % 2 ^ (b + 1) := ⟨_, rfl⟩
  obtain ⟨v2, hv2⟩ : ∃ v2, v2 = (v1 + 1 * (2 ^ (b + 1) - N)) % 2 ^ (b + 1) := ⟨_, rfl⟩
  obtain ⟨fb, hfb⟩ : ∃ fb, fb = v2 / A % 2 := ⟨_, rfl⟩
  obtain ⟨v3, hv3⟩ : ∃ v3, v3 = (v2 + fb * N) % 2 ^ (b + 1) := ⟨_, rfl⟩
  obtain ⟨v4, hv4⟩ : ∃ v4, v4 = (v3 + (2 ^ (b + 1) - x)) % 2 ^ (b + 1) := ⟨_, rfl⟩
  obtain ⟨hb, hhb⟩ : ∃ hb, hb = v4 / A % 2 := ⟨_, rfl⟩
  obtain ⟨v5, hv5⟩ : ∃ v5, v5 = (x + v4) % 2 ^ (b + 1) := ⟨_, rfl⟩
  have hv1lt : v1 < 2 ^ (b + 1) := by rw [hv1]; exact hlt _
  have hv2lt : v2 < 2 ^ (b + 1) := by rw [hv2]; exact hlt _
  have hv3lt : v3 < 2 ^ (b + 1) := by rw [hv3]; exact hlt _
  have hv4lt : v4 < 2 ^ (b + 1) := by rw [hv4]; exact hlt _
  have hylt : y < 2 ^ (b + 1) := by omega
  have harith := modAddQ_arith A N x y v1 v2 fb v3 v4 hb v5 hNA hx hy
    (by rw [hv1, hA2]) (by rw [hv2, hA2, one_mul]) hfb (by rw [hv3, hA2])
    (by rw [hv4, hA2]) hhb (by rw [hv5, hA2])
  have hfbval : ((fb : ℕ) : ZMod 2).val = fb := by
    rw [ZMod.val_natCast, hfb, Nat.mod_mod]
  have hflag0 : ((fb : ℕ) : ZMod 2) + natBits (b + 1) v4 (Fin.last b) + 1 = 0 := by
    have h0 : (((fb + hb + 1 : ℕ)) : ZMod 2) = 0 := by
      rw [← ZMod.natCast_mod (fb + hb + 1) 2, harith.1, Nat.cast_zero]
    push_cast at h0
    rw [hbit, ← hhb]
    exact h0
  have hupd0 : update β f 0 = β := by
    funext z
    by_cases h : z = f
    · rw [h, update_self, hf]
    · rw [update_of_ne h]
  -- the seven stages
  have s1 : runList (rippleSteps b rX rY ci rC)
      (writeReg (update β f 0) rY (natBits (b + 1) y)) =
      some (writeReg (update β f 0) rY (natBits (b + 1) v1)) := by
    rw [R 0 y hylt, hv1]
  have s2 : runList (caddcSteps b rY rK rC ci none (2 ^ (b + 1) - N))
      (writeReg (update β f 0) rY (natBits (b + 1) v1)) =
      some (writeReg (update β f 0) rY (natBits (b + 1) v2)) := by
    rw [K _ cN.1 cN.2.1 cN.2.2.1 cN.2.2.2 _ 0 v1 hv1lt, hcvN, h1v, hv2]
  have s3 : runList [Step.cnot (rY (Fin.last b)) f]
      (writeReg (update β f 0) rY (natBits (b + 1) v2)) =
      some (writeReg (update β f ((fb : ℕ) : ZMod 2)) rY (natBits (b + 1) v2)) := by
    rw [runList_cons, hrunC, Option.bind_some, runList_nil, hgetf, writeReg_apply_reg, hset,
      zero_add, hbit, hfb]
  have s4 : runList (caddcSteps b rY rK rC ci (some f) N)
      (writeReg (update β f ((fb : ℕ) : ZMod 2)) rY (natBits (b + 1) v2)) =
      some (writeReg (update β f ((fb : ℕ) : ZMod 2)) rY (natBits (b + 1) v3)) := by
    rw [K _ cF.1 cF.2.1 cF.2.2.1 cF.2.2.2 N _ v2 hv2lt, hcvF, hfbval, hv3]
  have s5 : runList ((rippleSteps b rX rY ci rC).reverse.map Step.inv)
      (writeReg (update β f ((fb : ℕ) : ZMod 2)) rY (natBits (b + 1) v3)) =
      some (writeReg (update β f ((fb : ℕ) : ZMod 2)) rY (natBits (b + 1) v4)) := by
    refine runList_inv (noUnxor_rippleSteps b rX rY ci rC) ?_
    rw [R _ v4 hv4lt, hv4, Nat.add_mod_mod,
      show x + (v3 + (2 ^ (b + 1) - x)) = v3 + 2 ^ (b + 1) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hv3lt]
  have s6 : runList [Step.cnot (rY (Fin.last b)) f, Step.x f]
      (writeReg (update β f ((fb : ℕ) : ZMod 2)) rY (natBits (b + 1) v4)) =
      some (writeReg (update β f 0) rY (natBits (b + 1) v4)) := by
    rw [runList_cons, hrunC, Option.bind_some, runList_cons, hrunX, Option.bind_some,
      runList_nil, update_self, update_idem, hgetf, writeReg_apply_reg, hset, hflag0]
  have s7 : runList (rippleSteps b rX rY ci rC)
      (writeReg (update β f 0) rY (natBits (b + 1) v4)) =
      some (writeReg (update β f 0) rY (natBits (b + 1) v5)) := by
    rw [R 0 v4 hv4lt, hv5]
  have hinit : writeReg β rY (natBits (b + 1) y) =
      writeReg (update β f 0) rY (natBits (b + 1) y) := by rw [hupd0]
  rw [hinit, modAddQSteps, runList_append, runList_append, runList_append, runList_append,
    runList_append, runList_append, s1, Option.bind_some, s2, Option.bind_some, s3,
    Option.bind_some, s4, Option.bind_some, s5, Option.bind_some, s6, Option.bind_some, s7,
    hupd0, harith.2]

theorem andCount_modAddQ (b N : ℕ) (rX rY rK : QRegister (b + 1) n) (rC : QRegister b n)
    (ci f : Wire n) :
    ((modAddQSteps b N rX rY rK rC ci f).map Step.andCount).sum = 5 * b := by
  simp only [modAddQSteps, List.map_append, List.sum_append, andCount_caddc,
    andCount_rippleSteps, andCount_ripple_inv, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Step.andCount]
  omega

/-!
### Sub-registers
-/

/-- A register on chosen wires of a larger register. -/
def subReg {T k : ℕ} (rAll : QRegister T n) (g : Fin k → Fin T) (hg : Injective g) :
    QRegister k n :=
  ⟨⟨fun i ↦ rAll (g i), rAll.wires.injective.comp hg⟩⟩

theorem subReg_disj {T k m : ℕ} (rAll : QRegister T n) (g : Fin k → Fin T) (hg : Injective g)
    (h : Fin m → Fin T) (hh : Injective h) (hgh : ∀ i j, (g i : ℕ) ≠ (h j : ℕ)) :
    (subReg rAll g hg).DisjointWires (subReg rAll h hh) :=
  QRegister.disjoint_iff.2 fun i j e ↦
    hgh i j (congrArg Fin.val (rAll.wires.injective (show rAll (g i) = rAll (h j) from e)))

theorem not_mem_subReg {T k : ℕ} (rAll : QRegister T n) (g : Fin k → Fin T) (hg : Injective g)
    (c : Fin T) (hc : ∀ i, (g i : ℕ) ≠ (c : ℕ)) : rAll c ∉ Set.range (subReg rAll g hg).wires := by
  rintro ⟨i, hi⟩
  exact hc i (congrArg Fin.val (rAll.wires.injective (show rAll (g i) = rAll c from hi)))


/-!
### Controlled modular addition of a constant

Load `c` into the source register under the control wire `e`, run the modular adder, unload.
-/

def cstepSteps (b N : ℕ) (rX rY rK : QRegister (b + 1) n) (rC : QRegister b n) (ci f e : Wire n)
    (c : ℕ) : List (Step n) :=
  xorSteps (some e) (b + 1) rX (natBits (b + 1) c) ++ modAddQSteps b N rX rY rK rC ci f ++
    xorSteps (some e) (b + 1) rX (natBits (b + 1) c)

theorem runList_cstep {b N : ℕ} {rX rY rK : QRegister (b + 1) n} {rC : QRegister b n}
    {ci f e : Wire n} (hL : Lay rX rY rK rC ci f) (hXK : rX.DisjointWires rK) (hNb : N ≤ 2 ^ b)
    (heX : e ∉ Set.range rX.wires) (heY : e ∉ Set.range rY.wires)
    (β : BitAssignment n) (hclean : Clean rK rC ci β) (hf : β f = 0) (hX0 : ∀ i, β (rX i) = 0)
    (c y : ℕ) (hc : c < N) (hy : y < N) :
    runList (cstepSteps b N rX rY rK rC ci f e c) (writeReg β rY (natBits (b + 1) y)) =
      some (writeReg β rY (natBits (b + 1) ((y + (β e).val * c) % N))) := by
  have hYX : rY.DisjointWires rX := QRegister.disjoint_comm.1 hL.hXY
  have heXi : ∀ i, CtrlNe (some e) (rX i) := fun i ↦ CtrlNe.some fun h ↦ heX ⟨i, h.symm⟩
  have hXnY : ∀ i, rX i ∉ Set.range rY.wires := fun i ↦ not_mem_of_disjoint hL.hXY i
  obtain ⟨hK0, hC0, hci0⟩ := hclean
  obtain ⟨u, hu⟩ : ∃ u, u = (β e).val * c := ⟨_, rfl⟩
  have hu1 : (β e).val ≤ 1 := by have := ZMod.val_lt (β e); omega
  have huc : u ≤ c := by
    rw [hu]
    calc (β e).val * c ≤ 1 * c := Nat.mul_le_mul_right c hu1
      _ = c := one_mul c
  have huN : u < N := lt_of_le_of_lt huc hc
  have hN2 : N ≤ 2 ^ (b + 1) := le_trans hNb (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hub : u < 2 ^ (b + 1) := lt_of_lt_of_le huN hN2
  have hγ : (fun i ↦ β e * natBits (b + 1) c i) = natBits (b + 1) u := by
    funext i
    rw [hu]
    have h1v : (1 : ZMod 2).val = 1 := rfl
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (β e) with h | h
    · rw [h]; simp [natBits]
    · rw [h]; simp [natBits, h1v]
  obtain ⟨β1, hβ1⟩ : ∃ β1, β1 = writeReg β rX (natBits (b + 1) u) := ⟨_, rfl⟩
  -- stage 1: load the constant under the control
  have h1 : runList (xorSteps (some e) (b + 1) rX (natBits (b + 1) c))
      (writeReg β rY (natBits (b + 1) y)) = some (writeReg β1 rY (natBits (b + 1) y)) := by
    rw [runList_xorSteps _ _ rX _ heXi]
    congr 1
    have hfun : (fun i ↦ writeReg β rY (natBits (b + 1) y) (rX i) +
        ctrlVal (some e) (writeReg β rY (natBits (b + 1) y)) * natBits (b + 1) c i) =
        natBits (b + 1) u := by
      rw [← hγ]
      funext i
      simp only [ctrlVal]
      rw [writeReg_apply_of_not_mem _ _ _ _ (hXnY i), hX0 i, zero_add,
        writeReg_apply_of_not_mem _ _ _ _ heY]
    rw [hfun, hβ1, writeReg_comm _ _ _ hYX]
  -- stage 2: the modular adder with the loaded constant as source
  have hclean1 : Clean rK rC ci β1 := by
    refine ⟨fun i ↦ ?_, fun i ↦ ?_, ?_⟩
    · rw [hβ1, writeReg_apply_of_not_mem _ _ _ _
        (not_mem_of_disjoint (QRegister.disjoint_comm.1 hXK) i)]
      exact hK0 i
    · rw [hβ1, writeReg_apply_of_not_mem _ _ _ _
        (not_mem_of_disjoint (QRegister.disjoint_comm.1 hL.hXC) i)]
      exact hC0 i
    · rw [hβ1, writeReg_apply_of_not_mem _ _ _ _ hL.ciX]
      exact hci0
  have hf1 : β1 f = 0 := by rw [hβ1, writeReg_apply_of_not_mem _ _ _ _ hL.fX]; exact hf
  have hX1 : (localIdx rX β1 : ℕ) = u := by
    rw [hβ1, localIdx_writeReg, ← basisBits_mk_eq_natBits _ _ hub]
    simp
  have h2 := runList_modAddQ hL hNb β1 hclean1 hf1 u y hX1 huN hy
  -- stage 3: unload the constant
  have h3 : runList (xorSteps (some e) (b + 1) rX (natBits (b + 1) c))
      (writeReg β1 rY (natBits (b + 1) ((u + y) % N))) =
      some (writeReg β rY (natBits (b + 1) ((u + y) % N))) := by
    rw [runList_xorSteps _ _ rX _ heXi]
    congr 1
    have hfun : (fun i ↦ writeReg β1 rY (natBits (b + 1) ((u + y) % N)) (rX i) +
        ctrlVal (some e) (writeReg β1 rY (natBits (b + 1) ((u + y) % N))) *
          natBits (b + 1) c i) = fun i ↦ β (rX i) := by
      funext i
      simp only [ctrlVal]
      rw [writeReg_apply_of_not_mem _ _ _ _ (hXnY i), writeReg_apply_of_not_mem _ _ _ _ heY,
        hβ1, writeReg_apply_reg, writeReg_apply_of_not_mem _ _ _ _ heX, hX0 i, ← hγ]
      exact CharTwo.add_self_eq_zero _
    rw [hfun, writeReg_comm _ _ _ hYX, hβ1, writeReg_writeReg, writeReg_self]
  unfold cstepSteps
  rw [runList_append, runList_append, h1, Option.bind_some, h2, Option.bind_some, h3, hu,
    Nat.add_comm ((β e).val * c) y]

theorem andCount_cstep (b N : ℕ) (rX rY rK : QRegister (b + 1) n) (rC : QRegister b n)
    (ci f e : Wire n) (c : ℕ) :
    ((cstepSteps b N rX rY rK rC ci f e c).map Step.andCount).sum = 5 * b := by
  simp only [cstepSteps, List.map_append, List.sum_append, andCount_xorSteps, andCount_modAddQ]
    <;> omega

/-!
### Doubly controlled modular addition of a constant

Compute `e ∧ d` into the clean wire `t`, run the controlled modular addition on `t`, uncompute.
-/

def ccstepSteps (b N : ℕ) (rX rY rK : QRegister (b + 1) n) (rC : QRegister b n)
    (ci f t e d : Wire n) (c : ℕ) : List (Step n) :=
  Step.and4t e d t :: (cstepSteps b N rX rY rK rC ci f t c ++ [Step.unand e d t])

/-- Facts about the AND wire `t`: it avoids the adder registers. -/
structure TW {b : ℕ} (rX rY rK : QRegister (b + 1) n) (rC : QRegister b n) (ci f t : Wire n) :
    Prop where
  tX : t ∉ Set.range rX.wires
  tY : t ∉ Set.range rY.wires
  tK : t ∉ Set.range rK.wires
  tC : t ∉ Set.range rC.wires
  tci : t ≠ ci
  tf : t ≠ f

theorem runList_ccstep {b N : ℕ} {rX rY rK : QRegister (b + 1) n} {rC : QRegister b n}
    {ci f t e d : Wire n} (hL : Lay rX rY rK rC ci f) (hXK : rX.DisjointWires rK)
    (hNb : N ≤ 2 ^ b) (hT : TW rX rY rK rC ci f t)
    (hed : e ≠ d) (het : e ≠ t) (hdt : d ≠ t)
    (heY : e ∉ Set.range rY.wires) (hdY : d ∉ Set.range rY.wires)
    (β : BitAssignment n) (hclean : Clean rK rC ci β) (hf : β f = 0) (hX0 : ∀ i, β (rX i) = 0)
    (ht0 : β t = 0) (c y : ℕ) (hc : c < N) (hy : y < N) :
    runList (ccstepSteps b N rX rY rK rC ci f t e d c) (writeReg β rY (natBits (b + 1) y)) =
      some (writeReg β rY (natBits (b + 1) ((y + (β e * β d).val * c) % N))) := by
  obtain ⟨β1, hβ1⟩ : ∃ β1, β1 = update β t (β e * β d) := ⟨_, rfl⟩
  have hβ1t : β1 t = β e * β d := by rw [hβ1, update_self]
  have h1 : (Step.and4t e d t).run (writeReg β rY (natBits (b + 1) y)) =
      some (writeReg β1 rY (natBits (b + 1) y)) := by
    have hw : ∀ v ∉ Set.range rY.wires, writeReg β rY (natBits (b + 1) y) v = β v :=
      fun v hv ↦ writeReg_apply_of_not_mem _ _ _ _ hv
    simp only [Step.run]
    rw [if_pos ⟨hed, het, hdt⟩, hw t hT.tY, if_pos ht0, hw e heY, hw d hdY, hβ1,
      writeReg_update_of_not_mem _ _ _ hT.tY]
  have hclean1 : Clean rK rC ci β1 :=
    ⟨fun i ↦ by rw [hβ1, update_of_ne (fun h ↦ hT.tK ⟨i, h⟩)]; exact hclean.1 i,
     fun i ↦ by rw [hβ1, update_of_ne (fun h ↦ hT.tC ⟨i, h⟩)]; exact hclean.2.1 i,
     by rw [hβ1, update_of_ne hT.tci.symm]; exact hclean.2.2⟩
  have hf1 : β1 f = 0 := by rw [hβ1, update_of_ne hT.tf.symm]; exact hf
  have hX01 : ∀ i, β1 (rX i) = 0 := fun i ↦ by
    rw [hβ1, update_of_ne (fun h ↦ hT.tX ⟨i, h⟩)]; exact hX0 i
  have h2 := runList_cstep hL hXK hNb hT.tX hT.tY β1 hclean1 hf1 hX01 c y hc hy
  have hβt : update β t 0 = β := by rw [← ht0, update_eq_self]
  have h3 : ∀ r, (Step.unand e d t).run (writeReg β1 rY (natBits (b + 1) r)) =
      some (writeReg β rY (natBits (b + 1) r)) := by
    intro r
    have hw1 : ∀ v ∉ Set.range rY.wires, writeReg β1 rY (natBits (b + 1) r) v = β1 v :=
      fun v hv ↦ writeReg_apply_of_not_mem _ _ _ _ hv
    simp only [Step.run]
    rw [if_pos ⟨hed, het, hdt⟩, hw1 t hT.tY, hw1 e heY, hw1 d hdY, hβ1t, hβ1,
      update_of_ne het, update_of_ne hdt, if_pos rfl,
      ← writeReg_update_of_not_mem _ _ _ hT.tY, update_idem, hβt]
  unfold ccstepSteps
  rw [runList_cons, h1, Option.bind_some, runList_append, h2, Option.bind_some, runList_cons,
    h3, Option.bind_some, runList_nil, hβ1t]

theorem andCount_ccstep (b N : ℕ) (rX rY rK : QRegister (b + 1) n) (rC : QRegister b n)
    (ci f t e d : Wire n) (c : ℕ) :
    ((ccstepSteps b N rX rY rK rC ci f t e d c).map Step.andCount).sum = 5 * b + 1 := by
  simp only [ccstepSteps, List.map_cons, List.map_append, List.sum_cons, List.sum_append,
    andCount_cstep, List.map_nil, List.sum_nil, Step.andCount] <;> omega

/-!
### Controlled multiply-accumulate by a constant

`rY ← (rY + e * c * rD) mod N`: one doubly controlled modular addition of `c * 2^i mod N` per bit
`i` of `rD`, with the second control on `e`.
-/

def cmulAccSteps (b N c : ℕ) {m : ℕ} (rD : QRegister m n) (rX rY rK : QRegister (b + 1) n)
    (rC : QRegister b n) (ci f t e : Wire n) : List (Step n) :=
  (List.finRange m).flatMap fun i ↦
    ccstepSteps b N rX rY rK rC ci f t e (rD i) (c * 2 ^ (i : ℕ) % N)

theorem runList_cmulAcc {b N m : ℕ} {rX rY rK : QRegister (b + 1) n} {rC : QRegister b n}
    {ci f t e : Wire n} (rD : QRegister m n) (hL : Lay rX rY rK rC ci f)
    (hXK : rX.DisjointWires rK) (hNb : N ≤ 2 ^ b) (hN : 0 < N) (hT : TW rX rY rK rC ci f t)
    (het : e ≠ t) (heY : e ∉ Set.range rY.wires) (hDe : ∀ i, e ≠ rD i) (hDt : ∀ i, rD i ≠ t)
    (hDY : ∀ i, rD i ∉ Set.range rY.wires)
    (β : BitAssignment n) (hclean : Clean rK rC ci β) (hf : β f = 0) (hX0 : ∀ i, β (rX i) = 0)
    (ht0 : β t = 0) (c y : ℕ) (hy : y < N) :
    runList (cmulAccSteps b N c rD rX rY rK rC ci f t e) (writeReg β rY (natBits (b + 1) y)) =
      some (writeReg β rY (natBits (b + 1)
        ((y + (β e).val * (c * (localIdx rD β : ℕ))) % N))) := by
  have hflat : ∀ (L : List (Fin m)) (u : ℕ), u < N →
      runList (L.flatMap fun i ↦
          ccstepSteps b N rX rY rK rC ci f t e (rD i) (c * 2 ^ (i : ℕ) % N))
        (writeReg β rY (natBits (b + 1) u)) =
      some (writeReg β rY (natBits (b + 1)
        ((u + (L.map fun i ↦ (β e * β (rD i)).val * (c * 2 ^ (i : ℕ) % N)).sum) % N))) := by
    intro L
    induction L with
    | nil =>
      intro u hu
      simp only [List.flatMap_nil, List.map_nil, List.sum_nil, add_zero, Nat.mod_eq_of_lt hu,
        runList_nil]
    | cons i L ih =>
      intro u hu
      rw [List.flatMap_cons, runList_append,
        runList_ccstep hL hXK hNb hT (hDe i) het (hDt i) heY (hDY i) β hclean hf hX0 ht0 _ u
          (Nat.mod_lt _ hN) hu,
        Option.bind_some, ih _ (Nat.mod_lt _ hN), List.map_cons, List.sum_cons, Nat.mod_add_mod,
        add_assoc]
  have hval : ∀ x z : ZMod 2, (x * z).val = x.val * z.val := by decide
  unfold cmulAccSteps
  rw [hflat _ y hy]
  refine congrArg some (congrArg (writeReg β rY) (congrArg (natBits (b + 1)) ?_))
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).1
  rw [localIdx_val rD]
  simp only [hval, ← Fin.sum_univ_def, Nat.cast_add, Nat.cast_sum, Nat.cast_mul, ZMod.natCast_mod,
    Nat.cast_pow, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

theorem andCount_flatMap {α : Type} (L : List α) (F : α → List (Step n)) (k : ℕ)
    (hF : ∀ a, ((F a).map Step.andCount).sum = k) :
    ((L.flatMap F).map Step.andCount).sum = L.length * k := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, hF, ih, List.length_cons]
    ring

theorem andCount_cmulAcc (b N c : ℕ) {m : ℕ} (rD : QRegister m n)
    (rX rY rK : QRegister (b + 1) n) (rC : QRegister b n) (ci f t e : Wire n) :
    ((cmulAccSteps b N c rD rX rY rK rC ci f t e).map Step.andCount).sum = m * (5 * b + 1) := by
  unfold cmulAccSteps
  rw [andCount_flatMap (List.finRange m) _ (5 * b + 1)
    (fun i ↦ andCount_ccstep _ _ _ _ _ _ _ _ _ _ _ _), List.length_finRange]

theorem andCount_cswap (c w_clean : Wire n) (w : ℕ) (rA rB : QRegister w n) :
    ((cswapSteps c w_clean w rA rB).map Step.andCount).sum = w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    rw [cswapSteps, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Step.andCount] <;> omega

/-- The state after a controlled swap, as two register writes. -/
theorem cswap_eq {w : ℕ} (rA rB : QRegister w n) (γ β' : BitAssignment n) (c : ZMod 2)
    (hfr : ∀ v, v ∉ Set.range rA.wires → v ∉ Set.range rB.wires → β' v = γ v)
    (hA : ∀ i, β' (rA i) = γ (rA i) + c * (γ (rA i) + γ (rB i)))
    (hB : ∀ i, β' (rB i) = γ (rB i) + c * (γ (rA i) + γ (rB i))) :
    β' = writeReg (writeReg γ rA (fun i ↦ γ (rA i) + c * (γ (rA i) + γ (rB i)))) rB
      (fun i ↦ γ (rB i) + c * (γ (rA i) + γ (rB i))) := by
  funext q
  by_cases hqB : q ∈ Set.range rB.wires
  · obtain ⟨i, rfl⟩ := hqB
    rw [writeReg_apply_reg, hB]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hqB]
    by_cases hqA : q ∈ Set.range rA.wires
    · obtain ⟨i, rfl⟩ := hqA
      rw [writeReg_apply_reg, hA]
    · rw [writeReg_apply_of_not_mem _ _ _ _ hqA, hfr q hqA hqB]

/-!
### Layout inside the combined register

`rAll` is the `ℓ + b` data wires (`y` at `[0, b)`, the exponent `e` at `[b, b + ℓ)`) followed by
the `4 * b + 6` ancilla wires, with `o = ℓ + b`: the accumulator `[o, o + b]` (its low `b` wires
are swapped with `y`), the loaded constant `[o + b + 1, o + 2b + 1]`, the adder constant register
`[o + 2b + 2, o + 3b + 2]`, the carries `[o + 3b + 3, o + 4b + 2]`, carry-in `o + 4b + 3`, flag
`o + 4b + 4`, AND wire `o + 4b + 5`.
-/

theorem wire_ne' {T : ℕ} (rAll : QRegister T n) (a c : ℕ) (ha : a < T) (hc : c < T)
    (h : a ≠ c) : rAll ⟨a, ha⟩ ≠ rAll ⟨c, hc⟩ :=
  fun e ↦ h (congrArg Fin.val (rAll.wires.injective e))

def gD (ℓ b : ℕ) (i : Fin b) : Fin (ℓ + b + (4 * b + 6)) :=
  ⟨i, by have := i.isLt; omega⟩
def gE (ℓ b : ℕ) (j : Fin ℓ) : Fin (ℓ + b + (4 * b + 6)) :=
  ⟨b + j, by have := j.isLt; omega⟩
def gY (ℓ b : ℕ) (i : Fin (b + 1)) : Fin (ℓ + b + (4 * b + 6)) :=
  ⟨ℓ + b + i, by have := i.isLt; omega⟩
def gYl (ℓ b : ℕ) (i : Fin b) : Fin (ℓ + b + (4 * b + 6)) :=
  ⟨ℓ + b + i, by have := i.isLt; omega⟩
def gX (ℓ b : ℕ) (i : Fin (b + 1)) : Fin (ℓ + b + (4 * b + 6)) :=
  ⟨ℓ + 2 * b + 1 + i, by have := i.isLt; omega⟩
def gK (ℓ b : ℕ) (i : Fin (b + 1)) : Fin (ℓ + b + (4 * b + 6)) :=
  ⟨ℓ + 3 * b + 2 + i, by have := i.isLt; omega⟩
def gC (ℓ b : ℕ) (i : Fin b) : Fin (ℓ + b + (4 * b + 6)) :=
  ⟨ℓ + 4 * b + 3 + i, by have := i.isLt; omega⟩

theorem gD_inj (ℓ b : ℕ) : Injective (gD ℓ b) := fun i j h ↦
  Fin.ext (by have h' := congrArg Fin.val h; simp only [gD] at h'; omega)
theorem gE_inj (ℓ b : ℕ) : Injective (gE ℓ b) := fun i j h ↦
  Fin.ext (by have h' := congrArg Fin.val h; simp only [gE] at h'; omega)
theorem gY_inj (ℓ b : ℕ) : Injective (gY ℓ b) := fun i j h ↦
  Fin.ext (by have h' := congrArg Fin.val h; simp only [gY] at h'; omega)
theorem gYl_inj (ℓ b : ℕ) : Injective (gYl ℓ b) := fun i j h ↦
  Fin.ext (by have h' := congrArg Fin.val h; simp only [gYl] at h'; omega)
theorem gX_inj (ℓ b : ℕ) : Injective (gX ℓ b) := fun i j h ↦
  Fin.ext (by have h' := congrArg Fin.val h; simp only [gX] at h'; omega)
theorem gK_inj (ℓ b : ℕ) : Injective (gK ℓ b) := fun i j h ↦
  Fin.ext (by have h' := congrArg Fin.val h; simp only [gK] at h'; omega)
theorem gC_inj (ℓ b : ℕ) : Injective (gC ℓ b) := fun i j h ↦
  Fin.ext (by have h' := congrArg Fin.val h; simp only [gC] at h'; omega)

section Layout

variable {ℓ b : ℕ} (rAll : QRegister (ℓ + b + (4 * b + 6)) n)

def regD : QRegister b n := subReg rAll (gD ℓ b) (gD_inj ℓ b)
def regE : QRegister ℓ n := subReg rAll (gE ℓ b) (gE_inj ℓ b)
def regY : QRegister (b + 1) n := subReg rAll (gY ℓ b) (gY_inj ℓ b)
def regYl : QRegister b n := subReg rAll (gYl ℓ b) (gYl_inj ℓ b)
def regX : QRegister (b + 1) n := subReg rAll (gX ℓ b) (gX_inj ℓ b)
def regK : QRegister (b + 1) n := subReg rAll (gK ℓ b) (gK_inj ℓ b)
def regC : QRegister b n := subReg rAll (gC ℓ b) (gC_inj ℓ b)
def wireE (j : Fin ℓ) : Wire n := rAll (gE ℓ b j)
def wireCi : Wire n := rAll ⟨ℓ + 5 * b + 3, by omega⟩
def wireF : Wire n := rAll ⟨ℓ + 5 * b + 4, by omega⟩
def wireT : Wire n := rAll ⟨ℓ + 5 * b + 5, by omega⟩

theorem lay_layout :
    Lay (regX rAll) (regY rAll) (regK rAll) (regC rAll) (wireCi rAll) (wireF rAll) := by
  refine ⟨subReg_disj _ _ _ _ _ ?_, subReg_disj _ _ _ _ _ ?_, subReg_disj _ _ _ _ _ ?_,
    subReg_disj _ _ _ _ _ ?_, subReg_disj _ _ _ _ _ ?_,
    not_mem_subReg _ _ _ _ ?_, not_mem_subReg _ _ _ _ ?_, not_mem_subReg _ _ _ _ ?_,
    not_mem_subReg _ _ _ _ ?_, not_mem_subReg _ _ _ _ ?_, not_mem_subReg _ _ _ _ ?_,
    not_mem_subReg _ _ _ _ ?_, not_mem_subReg _ _ _ _ ?_,
    wire_ne' rAll _ _ _ _ (by omega)⟩
  all_goals first
    | (intro i j; have := i.isLt; have := j.isLt; simp only [gX, gY, gK, gC]; omega)
    | (intro i; have := i.isLt; simp only [gX, gY, gK, gC]; omega)

theorem lay_tw :
    TW (regX rAll) (regY rAll) (regK rAll) (regC rAll) (wireCi rAll) (wireF rAll)
      (wireT rAll) := by
  refine ⟨not_mem_subReg _ _ _ _ ?_, not_mem_subReg _ _ _ _ ?_, not_mem_subReg _ _ _ _ ?_,
    not_mem_subReg _ _ _ _ ?_, wire_ne' rAll _ _ _ _ (by omega),
    wire_ne' rAll _ _ _ _ (by omega)⟩
  all_goals (intro i; have := i.isLt; simp only [gX, gY, gK, gC]; omega)

theorem lay_extra :
    (regX rAll).DisjointWires (regK rAll) ∧ (regD rAll).DisjointWires (regY rAll) ∧
      (regD rAll).DisjointWires (regYl rAll) := by
  refine ⟨subReg_disj _ _ _ _ _ ?_, subReg_disj _ _ _ _ _ ?_, subReg_disj _ _ _ _ _ ?_⟩
  all_goals (intro i j; have := i.isLt; have := j.isLt; simp only [gD, gX, gY, gYl, gK]; omega)

theorem lay_t :
    wireT rAll ∉ Set.range (regD rAll).wires ∧ wireT rAll ∉ Set.range (regYl rAll).wires := by
  refine ⟨not_mem_subReg _ _ _ _ ?_, not_mem_subReg _ _ _ _ ?_⟩
  all_goals (intro i; have := i.isLt; simp only [gD, gYl]; omega)

theorem lay_e (j : Fin ℓ) :
    wireE rAll j ≠ wireT rAll ∧ wireE rAll j ∉ Set.range (regY rAll).wires ∧
      wireE rAll j ∉ Set.range (regD rAll).wires ∧
      wireE rAll j ∉ Set.range (regYl rAll).wires := by
  have hj := j.isLt
  refine ⟨wire_ne' rAll _ _ _ _ (by omega), not_mem_subReg _ _ _ _ ?_, not_mem_subReg _ _ _ _ ?_,
    not_mem_subReg _ _ _ _ ?_⟩
  all_goals (intro i; have := i.isLt; simp only [gD, gE, gY, gYl]; omega)

theorem lay_nD (k : ℕ) (hk : ℓ + b ≤ k) (hk' : k < ℓ + b + (4 * b + 6)) :
    rAll ⟨k, hk'⟩ ∉ Set.range (regD rAll).wires :=
  not_mem_subReg rAll (gD ℓ b) (gD_inj ℓ b) _ fun i ↦ by have := i.isLt; simp only [gD]; omega

end Layout

/-- The inverse multiplier used to clear the accumulator: `-G⁻¹ mod N`. -/
def invMod (N G : ℕ) : ℕ := (-((G : ZMod N)⁻¹)).val

theorem invMod_spec (N G : ℕ) (hN : 0 < N) (hcop : Nat.Coprime G N) (x : ℕ) :
    (x + invMod N G * (G * x % N)) % N = 0 := by
  have : NeZero N := ⟨hN.ne'⟩
  have hu : (G : ZMod N) * (G : ZMod N)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one G hcop
  have e1 : ((invMod N G : ℕ) : ZMod N) = -((G : ZMod N)⁻¹) := by
    unfold invMod
    exact ZMod.natCast_zmod_val _
  have e2 : ((G * x % N : ℕ) : ZMod N) = (G : ZMod N) * x := by
    rw [ZMod.natCast_mod, Nat.cast_mul]
  have h0 : ((x + invMod N G * (G * x % N) : ℕ) : ZMod N) = ((0 : ℕ) : ZMod N) := by
    rw [Nat.cast_add, Nat.cast_mul, e1, e2, Nat.cast_zero]
    calc (x : ZMod N) + -((G : ZMod N)⁻¹) * ((G : ZMod N) * x)
        = x - x * ((G : ZMod N) * (G : ZMod N)⁻¹) := by ring
      _ = 0 := by rw [hu]; ring
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h0
  rwa [Nat.zero_mod] at this

/-- One exponent bit `j`: `y ↦ G^(e_j) * y mod N` in place, controlled on the exponent wire:
controlled multiply-accumulate `G * y` into the zero accumulator, controlled swap with `y`, then
controlled multiply-accumulate with `G' = -G⁻¹ mod N`, which clears the accumulator. -/
def bitSteps (ℓ b N G G' : ℕ) (rAll : QRegister (ℓ + b + (4 * b + 6)) n) (j : Fin ℓ) :
    List (Step n) :=
  cmulAccSteps b N G (regD rAll) (regX rAll) (regY rAll) (regK rAll) (regC rAll) (wireCi rAll)
    (wireF rAll) (wireT rAll) (wireE rAll j) ++
  cswapSteps (wireE rAll j) (wireT rAll) b (regD rAll) (regYl rAll) ++
  cmulAccSteps b N G' (regD rAll) (regX rAll) (regY rAll) (regK rAll) (regC rAll) (wireCi rAll)
    (wireF rAll) (wireT rAll) (wireE rAll j)

/-- Modular exponentiation: one controlled in-place multiplication by `g^(2^j)` per exponent bit. -/
def modExpSteps (ℓ b N g : ℕ) (rAll : QRegister (ℓ + b + (4 * b + 6)) n) : List (Step n) :=
  (List.finRange ℓ).flatMap fun (j : Fin ℓ) ↦
    bitSteps ℓ b N (g ^ 2 ^ (j : ℕ)) (invMod N (g ^ 2 ^ (j : ℕ))) rAll j

theorem andCount_bit (ℓ b N G G' : ℕ) (rAll : QRegister (ℓ + b + (4 * b + 6)) n) (j : Fin ℓ) :
    ((bitSteps ℓ b N G G' rAll j).map Step.andCount).sum =
      b * (5 * b + 1) + b + b * (5 * b + 1) := by
  unfold bitSteps
  rw [List.map_append, List.map_append, List.sum_append, List.sum_append, andCount_cmulAcc,
    andCount_cmulAcc, andCount_cswap]

theorem andCount_modExp (ℓ b N g : ℕ) (rAll : QRegister (ℓ + b + (4 * b + 6)) n) :
    ((modExpSteps ℓ b N g rAll).map Step.andCount).sum =
      ℓ * (b * (5 * b + 1) + b + b * (5 * b + 1)) := by
  unfold modExpSteps
  rw [andCount_flatMap (List.finRange ℓ) _ _ (fun j ↦ andCount_bit _ _ _ _ _ _ _),
    List.length_finRange]

/-- One exponent bit on a state with zero ancillas and data `u < N`. -/
theorem run_bit (ℓ b N G G' : ℕ) (hN : 0 < N) (hNb : N ≤ 2 ^ b)
    (hinv : ∀ u, (u + G' * (G * u % N)) % N = 0)
    (rAll : QRegister (ℓ + b + (4 * b + 6)) n) (j : Fin ℓ) (γ : BitAssignment n)
    (hanc : ∀ (k : ℕ) (hk : ℓ + b ≤ k) (hk' : k < ℓ + b + (4 * b + 6)), γ (rAll ⟨k, hk'⟩) = 0)
    (u : ℕ) (hu : u < N) (hD : (localIdx (regD rAll) γ : ℕ) = u) :
    runList (bitSteps ℓ b N G G' rAll j) γ =
      some (writeReg γ (regD rAll) (natBits b (G ^ (γ (wireE rAll j)).val * u % N))) := by
  have hlay := lay_layout rAll
  have hT := lay_tw rAll
  obtain ⟨hXK, hDY_d, hDYl⟩ := lay_extra rAll
  obtain ⟨htD, htYl⟩ := lay_t rAll
  obtain ⟨het, heY, heD, heYl⟩ := lay_e rAll j
  have hDY : ∀ i, regD rAll i ∉ Set.range (regY rAll).wires := fun i ↦
    not_mem_of_disjoint hDY_d i
  have hDt : ∀ i, regD rAll i ≠ wireT rAll := fun i h ↦ htD ⟨i, h⟩
  have hDe : ∀ i, wireE rAll j ≠ regD rAll i := fun i h ↦ heD ⟨i, h.symm⟩
  have hYnD : ∀ k, regY rAll k ∉ Set.range (regD rAll).wires := fun k ↦
    not_mem_of_disjoint (QRegister.disjoint_comm.1 hDY_d) k
  have hDnYl : ∀ i, regD rAll i ∉ Set.range (regYl rAll).wires := fun i ↦
    not_mem_of_disjoint hDYl i
  have hYlast : regY rAll (Fin.last b) ∉ Set.range (regYl rAll).wires := fun ⟨j, hj⟩ ↦
    (Fin.castSucc_lt_last j).ne ((regY rAll).wires.injective
      (show regY rAll (Fin.castSucc j) = regY rAll (Fin.last b) from hj))
  have hub : u < 2 ^ b := lt_of_lt_of_le hu hNb
  -- the work wires of any state that is zero on the ancillas
  have hzero : ∀ δ : BitAssignment n, (∀ (k : ℕ) (hk : ℓ + b ≤ k)
      (hk' : k < ℓ + b + (4 * b + 6)), δ (rAll ⟨k, hk'⟩) = 0) →
      Clean (regK rAll) (regC rAll) (wireCi rAll) δ ∧ δ (wireF rAll) = 0 ∧
        (∀ i, δ (regX rAll i) = 0) ∧ (∀ i, δ (regY rAll i) = 0) ∧ δ (wireT rAll) = 0 :=
    fun δ hδ ↦
      ⟨⟨fun i ↦ hδ (ℓ + 3 * b + 2 + i) (by omega) (by have := i.isLt; omega),
        fun i ↦ hδ (ℓ + 4 * b + 3 + i) (by omega) (by have := i.isLt; omega),
        hδ (ℓ + 5 * b + 3) (by omega) (by omega)⟩,
       hδ (ℓ + 5 * b + 4) (by omega) (by omega),
       fun i ↦ hδ (ℓ + 2 * b + 1 + i) (by omega) (by have := i.isLt; omega),
       fun i ↦ hδ (ℓ + b + i) (by omega) (by have := i.isLt; omega),
       hδ (ℓ + 5 * b + 5) (by omega) (by omega)⟩
  have hstart : ∀ δ : BitAssignment n, (∀ i, δ (regY rAll i) = 0) →
      δ = writeReg δ (regY rAll) (natBits (b + 1) 0) := by
    intro δ hδ
    have h0 : natBits (b + 1) 0 = fun i ↦ δ (regY rAll i) := funext fun i ↦ by
      rw [hδ i]; simp [natBits]
    rw [h0, writeReg_self]
  have hbit : ∀ i, γ (regD rAll i) = natBits b u i := fun i ↦ by
    have h : basisBits b (localIdx (regD rAll) γ) i = γ (regD rAll i) := by
      rw [localIdx, Equiv.apply_symm_apply]
    rw [← h, basisBits_eq_div_mod, hD]
    rfl
  have hγD : γ = writeReg γ (regD rAll) (natBits b u) := by
    rw [show natBits b u = fun i ↦ γ (regD rAll i) from funext fun i ↦ (hbit i).symm,
      writeReg_self]
  obtain ⟨hcl, hf, hX0, hY0, ht0⟩ := hzero γ hanc
  -- pass 1
  have h1 := runList_cmulAcc (regD rAll) hlay hXK hNb hN hT het heY hDe hDt hDY γ hcl hf hX0 ht0
    G 0 hN
  rw [← hstart γ hY0, zero_add, hD] at h1
  obtain ⟨r1, hr1⟩ : ∃ r1, r1 = (γ (wireE rAll j)).val * (G * u) % N := ⟨_, rfl⟩
  rw [← hr1] at h1
  have hr1b : r1 < 2 ^ b := by rw [hr1]; exact lt_of_lt_of_le (Nat.mod_lt _ hN) hNb
  obtain ⟨γ1, hγ1⟩ : ∃ γ1, γ1 = writeReg γ (regY rAll) (natBits (b + 1) r1) := ⟨_, rfl⟩
  rw [← hγ1] at h1
  have hγ1t : γ1 (wireT rAll) = 0 := by
    rw [hγ1, writeReg_apply_of_not_mem _ _ _ _ hT.tY, ht0]
  have hγ1e : γ1 (wireE rAll j) = γ (wireE rAll j) := by
    rw [hγ1, writeReg_apply_of_not_mem _ _ _ _ heY]
  -- the controlled swap
  obtain ⟨β', hrun2, hfr, hA, hB⟩ := runList_cswapSteps (wireE rAll j) (wireT rAll) b
    (regD rAll) (regYl rAll) hDYl heD heYl het htD htYl γ1 hγ1t
  have hβ' := cswap_eq (regD rAll) (regYl rAll) γ1 β' _ hfr hA hB
  rw [hγ1e] at hβ'
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (γ (wireE rAll j)) with h0 | h1'
  · -- control off: everything is the identity
    have hs : (γ (wireE rAll j)).val = 0 := by rw [h0]; rfl
    rw [hs, zero_mul, Nat.zero_mod] at hr1
    have hγ1γ : γ1 = γ := by rw [hγ1, hr1, ← hstart γ hY0]
    simp only [h0, zero_mul, add_zero, writeReg_self] at hβ'
    have h3 := runList_cmulAcc (regD rAll) hlay hXK hNb hN hT het heY hDe hDt hDY γ hcl hf hX0
      ht0 G' 0 hN
    rw [← hstart γ hY0, hs, zero_mul, add_zero, Nat.zero_mod, ← hstart γ hY0] at h3
    unfold bitSteps
    rw [runList_append, runList_append, h1, Option.bind_some, hrun2, Option.bind_some, hβ',
      hγ1γ, h3, hs, pow_zero, one_mul, Nat.mod_eq_of_lt hu, ← hγD]
  · -- control on: multiply, swap, clear
    have hs : (γ (wireE rAll j)).val = 1 := by rw [h1']; rfl
    rw [hs, one_mul] at hr1
    have e1 : ∀ x z : ZMod 2, x + (x + z) = z := by decide
    have e2 : ∀ x z : ZMod 2, z + (x + z) = x := by decide
    simp only [h1', one_mul, e1, e2] at hβ'
    obtain ⟨γ', hγ'⟩ : ∃ γ', γ' = writeReg γ (regD rAll) (natBits b r1) := ⟨_, rfl⟩
    have hswap : writeReg (writeReg γ1 (regD rAll) (fun i ↦ γ1 (regYl rAll i))) (regYl rAll)
        (fun i ↦ γ1 (regD rAll i)) = writeReg γ' (regY rAll) (natBits (b + 1) u) := by
      funext q
      by_cases hqY : q ∈ Set.range (regY rAll).wires
      · obtain ⟨k, rfl⟩ := hqY
        rw [show writeReg γ' (regY rAll) (natBits (b + 1) u) (regY rAll k) =
          natBits (b + 1) u k from writeReg_apply_reg _ _ _ _]
        cases k using Fin.lastCases with
        | last =>
          rw [writeReg_apply_of_not_mem _ _ _ _ hYlast,
            writeReg_apply_of_not_mem _ _ _ _ (hYnD _), hγ1, writeReg_apply_reg]
          simp only [natBits, Fin.val_last, Nat.div_eq_of_lt hr1b, Nat.div_eq_of_lt hub]
        | cast k =>
          have e3 : regY rAll (Fin.castSucc k) = regYl rAll k := rfl
          rw [e3, writeReg_apply_reg]
          show γ1 (regD rAll k) = natBits (b + 1) u (Fin.castSucc k)
          rw [hγ1, writeReg_apply_of_not_mem _ _ _ _ (hDY k), hbit k]
          rfl
      · rw [writeReg_apply_of_not_mem _ _ _ _ hqY]
        by_cases hqD : q ∈ Set.range (regD rAll).wires
        · obtain ⟨i, rfl⟩ := hqD
          rw [writeReg_apply_of_not_mem _ _ _ _ (hDnYl i), writeReg_apply_reg]
          show γ1 (regYl rAll i) = γ' (regD rAll i)
          rw [hγ1, hγ', writeReg_apply_reg]
          exact writeReg_apply_reg γ (regY rAll) (natBits (b + 1) r1) (Fin.castSucc i)
        · have hqYl : q ∉ Set.range (regYl rAll).wires := fun ⟨k, hk⟩ ↦
            hqY ⟨Fin.castSucc k, hk⟩
          rw [writeReg_apply_of_not_mem _ _ _ _ hqYl, writeReg_apply_of_not_mem _ _ _ _ hqD, hγ1,
            hγ', writeReg_apply_of_not_mem _ _ _ _ hqY, writeReg_apply_of_not_mem _ _ _ _ hqD]
    -- pass 2 from `γ'`
    have hanc' : ∀ (k : ℕ) (hk : ℓ + b ≤ k) (hk' : k < ℓ + b + (4 * b + 6)),
        γ' (rAll ⟨k, hk'⟩) = 0 := fun k hk hk' ↦ by
      rw [hγ', writeReg_apply_of_not_mem _ _ _ _ (lay_nD rAll k hk hk')]
      exact hanc k hk hk'
    obtain ⟨hcl', hf', hX0', hY0', ht0'⟩ := hzero γ' hanc'
    have hDidx' : (localIdx (regD rAll) γ' : ℕ) = r1 := by
      rw [hγ', localIdx_writeReg, ← basisBits_mk_eq_natBits _ _ hr1b]
      simp
    have hγ'e : γ' (wireE rAll j) = γ (wireE rAll j) := by
      rw [hγ', writeReg_apply_of_not_mem _ _ _ _ heD]
    have h3 := runList_cmulAcc (regD rAll) hlay hXK hNb hN hT het heY hDe hDt hDY γ' hcl' hf'
      hX0' ht0' G' u hu
    rw [hDidx', hγ'e, hs, one_mul, hr1, hinv u, ← hstart γ' hY0'] at h3
    unfold bitSteps
    rw [runList_append, runList_append, h1, Option.bind_some, hrun2, Option.bind_some, hβ',
      hswap, h3, hγ', hs, pow_one, hr1]

/-- All exponent bits in a list, from data `u < N` with zero ancillas. -/
theorem run_chain (ℓ b N g : ℕ) (hN : 0 < N) (hNb : N ≤ 2 ^ b) (hcop : Nat.Coprime g N)
    (rAll : QRegister (ℓ + b + (4 * b + 6)) n) (β0 : BitAssignment n)
    (hanc : ∀ (k : ℕ) (hk : ℓ + b ≤ k) (hk' : k < ℓ + b + (4 * b + 6)), β0 (rAll ⟨k, hk'⟩) = 0) :
    ∀ (L : List (Fin ℓ)) (u : ℕ), u < N →
      runList (L.flatMap fun (j : Fin ℓ) ↦
          bitSteps ℓ b N (g ^ 2 ^ (j : ℕ)) (invMod N (g ^ 2 ^ (j : ℕ))) rAll j)
        (writeReg β0 (regD rAll) (natBits b u)) =
      some (writeReg β0 (regD rAll) (natBits b
        ((L.map fun (j : Fin ℓ) ↦ (g ^ 2 ^ (j : ℕ)) ^ (β0 (wireE rAll j)).val).prod * u % N))) := by
  intro L
  induction L with
  | nil =>
    intro u hu
    simp only [List.flatMap_nil, runList_nil, List.map_nil, List.prod_nil, one_mul,
      Nat.mod_eq_of_lt hu]
  | cons j L ih =>
    intro u hu
    have hub : u < 2 ^ b := lt_of_lt_of_le hu hNb
    have hanc' : ∀ (k : ℕ) (hk : ℓ + b ≤ k) (hk' : k < ℓ + b + (4 * b + 6)),
        writeReg β0 (regD rAll) (natBits b u) (rAll ⟨k, hk'⟩) = 0 := fun k hk hk' ↦ by
      rw [writeReg_apply_of_not_mem _ _ _ _ (lay_nD rAll k hk hk')]
      exact hanc k hk hk'
    have hD' : (localIdx (regD rAll) (writeReg β0 (regD rAll) (natBits b u)) : ℕ) = u := by
      rw [localIdx_writeReg, ← basisBits_mk_eq_natBits _ _ hub]
      simp
    have hγ := run_bit ℓ b N _ _ hN hNb
      (invMod_spec N (g ^ 2 ^ (j : ℕ)) hN (Nat.Coprime.pow_left _ hcop)) rAll j
      (writeReg β0 (regD rAll) (natBits b u)) hanc' u hu hD'
    rw [writeReg_apply_of_not_mem _ _ _ _ (lay_e rAll j).2.2.1, writeReg_writeReg] at hγ
    rw [List.flatMap_cons, runList_append, hγ, Option.bind_some, ih _ (Nat.mod_lt _ hN),
      List.map_cons, List.prod_cons]
    refine congrArg some (congrArg (writeReg β0 (regD rAll)) (congrArg (natBits b) ?_))
    apply (ZMod.natCast_eq_natCast_iff' _ _ _).1
    simp only [Nat.cast_mul, ZMod.natCast_mod]
    ring

theorem split_symm_val (ℓ b : ℕ) (e : Fin (2 ^ ℓ)) (y : Fin (2 ^ b)) :
    (((splitBasisEquiv ℓ b).symm (e, y) : Fin (2 ^ (ℓ + b))) : ℕ) = y + 2 ^ b * e := by
  first | rfl | simp [splitBasisEquiv]

theorem bit_low (L t i m : ℕ) (him : i < m) :
    (L + 2 ^ m * t) / 2 ^ i % 2 = L / 2 ^ i % 2 := by
  have hm : 2 ^ m = 2 ^ i * 2 ^ (m - i) := by rw [← pow_add]; congr 1; omega
  have hpos : 0 < 2 ^ i := by positivity
  have h0 : 2 ^ (m - i) * t % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) t)
  rw [hm, mul_assoc, Nat.add_mul_div_left _ _ hpos, Nat.add_mod, h0, add_zero, Nat.mod_mod]

theorem bit_high (L t m j : ℕ) (hL : L < 2 ^ m) :
    (L + 2 ^ m * t) / 2 ^ (m + j) = t / 2 ^ j := by
  have hpos : 0 < 2 ^ m := by positivity
  rw [pow_add, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hL,
    zero_add]

theorem bit_high' (L t m i : ℕ) (hL : L < 2 ^ m) (hi : m ≤ i) :
    (L + 2 ^ m * t) / 2 ^ i % 2 = t / 2 ^ (i - m) % 2 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [bit_high L t m j hL, Nat.add_sub_cancel_left]

/-- On data `y + 2^b * e` with `y < N` and zero ancillas, the placed program writes
`g^e * y mod N + 2^b * e` into the data register. -/
theorem run_modExpProg (ℓ b N g : ℕ) (hN : 0 < N) (hNb : N ≤ 2 ^ b) (hcop : Nat.Coprime g N)
    (rData : QRegister (ℓ + b) n) (rAnc : QRegister (4 * b + 6) n)
    (hdisj : rData.DisjointWires rAnc) (β : BitAssignment n) (hanc : localIdx rAnc β = 0)
    (e y : ℕ) (he : e < 2 ^ ℓ) (hyN : y < N)
    (hLval : (localIdx rData β : ℕ) = y + 2 ^ b * e)
    (J : Fin (2 ^ (ℓ + b))) (hJ : (J : ℕ) = g ^ e * y % N + 2 ^ b * e) :
    runList (modExpSteps ℓ b N g (rData.concat rAnc hdisj)) β =
      some (writeReg β rData (basisBits (ℓ + b) J)) := by
  have hyb : y < 2 ^ b := lt_of_lt_of_le hyN hNb
  obtain ⟨rAll, hrAll⟩ : ∃ r, r = rData.concat rAnc hdisj := ⟨_, rfl⟩
  rw [← hrAll]
  have hL : ∀ i : Fin (ℓ + b), rAll (Fin.castAdd (4 * b + 6) i) = rData i := fun i ↦ by
    rw [hrAll]; exact QRegister.concat_apply_left rData rAnc hdisj i
  have hR : ∀ i : Fin (4 * b + 6), rAll (Fin.natAdd (ℓ + b) i) = rAnc i := fun i ↦ by
    rw [hrAll]; exact QRegister.concat_apply_right rData rAnc hdisj i
  have hanc0 : ∀ (k : ℕ) (hk : ℓ + b ≤ k) (hk' : k < ℓ + b + (4 * b + 6)),
      β (rAll ⟨k, hk'⟩) = 0 := fun k hk hk' ↦ by
    have hk2 : (⟨k, hk'⟩ : Fin (ℓ + b + (4 * b + 6))) =
        Fin.natAdd (ℓ + b) ⟨k - (ℓ + b), by omega⟩ := Fin.ext (by
      show k = ℓ + b + (k - (ℓ + b))
      omega)
    rw [hk2, hR]
    exact anc_bits_zero rAnc β hanc _
  have hbitD : ∀ i : Fin (ℓ + b), β (rData i) =
      (((localIdx rData β : ℕ) / 2 ^ (i : ℕ) % 2 : ℕ) : ZMod 2) := fun i ↦ by
    have h : basisBits (ℓ + b) (localIdx rData β) i = β (rData i) := by
      rw [localIdx, Equiv.apply_symm_apply]
    rw [← h, basisBits_eq_div_mod]
  have hDdat : ∀ i : Fin b, regD rAll i = rData ⟨i, by have := i.isLt; omega⟩ := fun i ↦
    hL ⟨i, by have := i.isLt; omega⟩
  have hEdat : ∀ j : Fin ℓ, wireE rAll j = rData ⟨b + j, by have := j.isLt; omega⟩ := fun j ↦
    hL ⟨b + j, by have := j.isLt; omega⟩
  have hDbit : ∀ i : Fin b, β (regD rAll i) = ((y / 2 ^ (i : ℕ) % 2 : ℕ) : ZMod 2) := fun i ↦ by
    rw [hDdat, hbitD]
    show ((_ / 2 ^ (i : ℕ) % 2 : ℕ) : ZMod 2) = _
    rw [hLval, bit_low _ _ _ _ i.isLt]
  have hEbit : ∀ j : Fin ℓ, β (wireE rAll j) = ((e / 2 ^ (j : ℕ) % 2 : ℕ) : ZMod 2) :=
    fun j ↦ by
      rw [hEdat, hbitD]
      show ((_ / 2 ^ (b + (j : ℕ)) % 2 : ℕ) : ZMod 2) = _
      rw [hLval, bit_high _ _ _ _ hyb]
  have hEidx : (localIdx (regE rAll) β : ℕ) = e := by
    have h : localIdx (regE rAll) β = ⟨e, he⟩ := by
      rw [localIdx, Equiv.symm_apply_eq, basisBits_mk_eq_natBits]
      funext j
      exact hEbit j
    rw [h]
  have hP : ((List.finRange ℓ).map fun (j : Fin ℓ) ↦ (g ^ 2 ^ (j : ℕ)) ^ (β (wireE rAll j)).val).prod =
      g ^ e := by
    rw [← Fin.prod_univ_def]
    simp only [← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum, ← hEidx, localIdx_val]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    show 2 ^ (j : ℕ) * (β (wireE rAll j)).val = (β (wireE rAll j)).val * 2 ^ (j : ℕ)
    ring
  have hstart : β = writeReg β (regD rAll) (natBits b y) := by
    rw [show natBits b y = fun i ↦ β (regD rAll i) from funext fun i ↦ (hDbit i).symm,
      writeReg_self]
  have hfinal : ∀ (r : ℕ) (hr : r < 2 ^ b) (J : Fin (2 ^ (ℓ + b))) (hJ : (J : ℕ) = r + 2 ^ b * e),
      writeReg β (regD rAll) (natBits b r) = writeReg β rData (basisBits (ℓ + b) J) := by
    intro r hr J hJ
    funext q
    by_cases hq : q ∈ Set.range rData.wires
    · obtain ⟨i, rfl⟩ := hq
      have hi2 := i.isLt
      rw [writeReg_apply_reg, basisBits_eq_div_mod, hJ]
      by_cases hi : (i : ℕ) < b
      · have hDw : rData i = regD rAll ⟨i, hi⟩ := (hDdat ⟨i, hi⟩).symm
        rw [hDw, writeReg_apply_reg]
        show ((r / 2 ^ (i : ℕ) % 2 : ℕ) : ZMod 2) = _
        rw [bit_low _ _ _ _ hi]
      · have hi' : b ≤ (i : ℕ) := by omega
        have hnm : rData i ∉ Set.range (regD rAll).wires := by
          rw [← hL i]
          refine not_mem_subReg rAll (gD ℓ b) (gD_inj ℓ b) _ fun k ↦ ?_
          have := k.isLt
          show (k : ℕ) ≠ (i : ℕ)
          omega
        rw [writeReg_apply_of_not_mem _ _ _ _ hnm, hbitD i, hLval, bit_high' _ _ _ _ hyb hi',
          bit_high' _ _ _ _ hr hi']
    · have hqD : q ∉ Set.range (regD rAll).wires := fun ⟨k, hk⟩ ↦
        hq ⟨_, (hDdat k).symm.trans hk⟩
      rw [writeReg_apply_of_not_mem _ _ _ _ hq, writeReg_apply_of_not_mem _ _ _ _ hqD]
  have hrun := run_chain ℓ b N g hN hNb hcop rAll β hanc0 (List.finRange ℓ) y hyN
  rw [← hstart, hP] at hrun
  unfold modExpSteps
  rw [hrun, hfinal _ (lt_of_lt_of_le (Nat.mod_lt _ hN) hNb) J hJ]

end ModExpImpl

open ModExpImpl ArcsinImpl OnEncodingBridge

theorem ModExpImpl.run_modExpProg' {n : ℕ} (p : ModExpParams) (rData : QRegister (p.ℓ + p.b) n)
    (rAnc : QRegister (4 * p.b + 6) n) (hdisj : rData.DisjointWires rAnc) (β : BitAssignment n)
    (hanc : localIdx rAnc β = 0) (hv : localIdx rData β ∈ modExpValidInputs p) :
    runList (modExpSteps p.ℓ p.b p.N p.g (rData.concat rAnc hdisj)) β =
      some (writeReg β rData (basisBits (p.ℓ + p.b) (modExpPerm p (localIdx rData β)))) := by
  obtain ⟨⟨e, y⟩, hP⟩ : ∃ P, P = splitBasisEquiv p.ℓ p.b (localIdx rData β) := ⟨_, rfl⟩
  have hidx : localIdx rData β = (splitBasisEquiv p.ℓ p.b).symm (e, y) := by
    rw [hP, Equiv.symm_apply_apply]
  have hv' := hv
  rw [hidx] at hv'
  simp only [modExpValidInputs, Set.mem_setOf_eq, Equiv.apply_symm_apply] at hv'
  have hσ : modExpPerm p (localIdx rData β) = (splitBasisEquiv p.ℓ p.b).symm
      (e, ⟨p.g ^ (e : ℕ) * y % p.N, lt_of_lt_of_le (Nat.mod_lt _ p.hN) p.hNb⟩) := by
    rw [Equiv.eq_symm_apply, hidx]
    exact modExpPerm_apply_valid p e y hv'
  rw [hσ]
  exact run_modExpProg p.ℓ p.b p.N p.g p.hN p.hNb p.hcop rData rAnc hdisj β hanc e y e.isLt hv'
    (by rw [hidx, split_symm_val]) _ (by rw [split_symm_val])

open ArcsinImpl OnEncodingBridge


/-- Number of clean ancilla qubits `modExpProgram` uses for parameters `p`. -/
def modExpAncillas (p : ModExpParams) : ℕ := 4 * p.b + 6

/-- Parameterized modular-exponentiation circuit on `p.ℓ + p.b` data wires `rData` (`p.b` target
wires `y` followed by `p.ℓ` exponent wires `e`, each little-endian, matching `finProdFinEquiv`
as in `tableAddPerm`) and `modExpAncillas p` clean ancilla wires `rAnc`. -/
def modExpProgram {n : ℕ} (p : ModExpParams)
    (rData : QRegister (p.ℓ + p.b) n)
    (rAnc : QRegister (modExpAncillas p) n) : DynamicCircuit Var n :=
  if h : ∀ i j, rData i ≠ rAnc j then
    compileList v (modExpSteps p.ℓ p.b p.N p.g (rData.concat rAnc (QRegister.disjoint_iff.2 h)))
  else .identity

/-- Parameterized correctness theorem: for all widths, modulus `1 ≤ N ≤ 2^b` and base `g`
coprime to `N`, `modExpProgram p` maps every valid input `|e⟩|y⟩` (`y < N`) with clean ancillas
to `|e⟩|g^e * y mod N⟩` with clean ancillas, across all disjoint register placements. -/
theorem modExp_correctness (p : ModExpParams) :
    ∀ {n : ℕ}
      (rData : QRegister (p.ℓ + p.b) n)
      (rAnc : QRegister (modExpAncillas p) n)
      (hdisj : rData.DisjointWires rAnc),
      RealizesCleanSubroutineOnEncoding rData rAnc hdisj (modExpValidInputs p) (modExpPerm p)
        (modExpProgram p rData rAnc).compile := by
  intro n rData rAnc hdisj
  have h : ∀ i j, rData i ≠ rAnc j := QRegister.disjoint_iff.1 hdisj
  have hprog : modExpProgram p rData rAnc =
      compileList v (modExpSteps p.ℓ p.b p.N p.g (rData.concat rAnc hdisj)) := by
    rw [modExpProgram, dite_eq_left h]
  rw [hprog]
  obtain ⟨R, hK, hR, -⟩ := exists_lowerKraus_compileList v
    (modExpSteps p.ℓ p.b p.N p.g (rData.concat rAnc hdisj))
  exact realizesCleanSubroutineOnEncoding_of_lowerKraus rData rAnc hdisj _ _ hK
    fun β hβ hv ↦ hR β _ (ModExpImpl.run_modExpProg' p rData rAnc hdisj β hβ hv)

/-- `T`-gate count of `modExpProgram p`. -/
abbrev modExpTCount {n : ℕ} (p : ModExpParams)
    (rData : QRegister (p.ℓ + p.b) n)
    (rAnc : QRegister (modExpAncillas p) n) : ℕ :=
  (modExpProgram p rData rAnc).count PrimitiveGate.T

/-- Spacetime cost `T count * qubits` of `modExpProgram p`, counting all
`p.ℓ + p.b + modExpAncillas p` data and clean ancilla qubits. -/
abbrev modExpSpacetime {n : ℕ} (p : ModExpParams)
    (rData : QRegister (p.ℓ + p.b) n)
    (rAnc : QRegister (modExpAncillas p) n) : ℕ :=
  modExpTCount p rData rAnc * (p.ℓ + p.b + modExpAncillas p)

/-!
## Cost Theorems

Both forbid primitive `TOFF` gates and hold uniformly over every modulus and every coprime base
at `ℓ = 1280`, `b = 2048`.
-/

/-- At widths `ℓ` and `b`, for every modulus and coprime base, `modExpProgram` uses no primitive
`TOFF` gates and has spacetime cost at most `cost` across all register placements. -/
abbrev SatisfiesModExpSpacetimeBound (ℓ b cost : ℕ) : Prop :=
  ∀ (p : ModExpParams), p.ℓ = ℓ → p.b = b →
    ∀ {n : ℕ}
      (rData : QRegister (p.ℓ + p.b) n)
      (rAnc : QRegister (modExpAncillas p) n),
      (modExpProgram p rData rAnc).count PrimitiveGate.TOFF = 0 ∧
        modExpSpacetime p rData rAnc ≤ cost

/-- At widths `ℓ` and `b`, for every modulus and coprime base, `modExpProgram` uses no primitive
`TOFF` gates and at most `cost` `T` gates across all register placements. -/
abbrev SatisfiesModExpTCountBound (ℓ b cost : ℕ) : Prop :=
  ∀ (p : ModExpParams), p.ℓ = ℓ → p.b = b →
    ∀ {n : ℕ}
      (rData : QRegister (p.ℓ + p.b) n)
      (rAnc : QRegister (modExpAncillas p) n),
      (modExpProgram p rData rAnc).count PrimitiveGate.TOFF = 0 ∧
        modExpTCount p rData rAnc ≤ cost

theorem ModExpImpl.modExpProgram_count {n : ℕ} (p : ModExpParams)
    (rData : QRegister (p.ℓ + p.b) n) (rAnc : QRegister (modExpAncillas p) n) :
    (modExpProgram p rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (modExpProgram p rData rAnc).count PrimitiveGate.T ≤
        4 * (p.ℓ * (p.b * (5 * p.b + 1) + p.b + p.b * (5 * p.b + 1))) := by
  by_cases h : ∀ i j, rData i ≠ rAnc j
  · rw [modExpProgram, dite_eq_left h]
    refine ⟨count_TOFF_compileList _ _, (count_T_compileList _ _).trans ?_⟩
    rw [andCount_modExp]
  · rw [modExpProgram, dite_eq_right h]
    exact ⟨rfl, Nat.zero_le _⟩

/-- Claimed spacetime cost bound at `ℓ = 1280`, `b = 2048`. -/
def modExpL1280B2048SpacetimeCost : ℕ := 2475552229294080

theorem modExp_l1280_b2048_spacetime_cost :
    SatisfiesModExpSpacetimeBound 1280 2048 modExpL1280B2048SpacetimeCost := by
  intro p hl hp n rData rAnc
  obtain ⟨h0, hT⟩ := ModExpImpl.modExpProgram_count p rData rAnc
  refine ⟨h0, ?_⟩
  calc modExpSpacetime p rData rAnc ≤
        4 * (p.ℓ * (p.b * (5 * p.b + 1) + p.b + p.b * (5 * p.b + 1))) *
          (p.ℓ + p.b + modExpAncillas p) :=
        Nat.mul_le_mul_right _ hT
    _ = modExpL1280B2048SpacetimeCost := by rw [modExpAncillas, hl, hp]; rfl

/-- Claimed `T`-count bound at `ℓ = 1280`, `b = 2048`. -/
def modExpL1280B2048TCountCost : ℕ := 214779822080

theorem modExp_l1280_b2048_t_count_cost :
    SatisfiesModExpTCountBound 1280 2048 modExpL1280B2048TCountCost := by
  intro p hl hp n rData rAnc
  obtain ⟨h0, hT⟩ := ModExpImpl.modExpProgram_count p rData rAnc
  refine ⟨h0, hT.trans ?_⟩
  rw [hl, hp]
  decide

end QuantumComputation.Specs
