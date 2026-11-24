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
# ModMulConst baseline (non-vacuous)

The frozen `QuantumSpecs/ModularArithmetic/ModMulConst.lean` with its holes filled by a textbook in-place modular
multiplier by a constant on `5 * b + 5` qubits: multiply-accumulate `a * x mod N` into a zero
accumulator with one controlled modular addition per bit of `x`, swap the accumulator with `x`,
then multiply-accumulate with `-a⁻¹ mod N`, which returns the accumulator to zero. Each
controlled modular addition loads the constant under the control bit, runs the modular adder of
`QuantumSolutions/ModularArithmetic/ModAdd.lean`, and unloads the constant. Correctness is proved for every width `b`,
modulus `1 ≤ N ≤ 2^b` and multiplier coprime to `N`; the `T` count is at most `40 * b^2`.

Credits: the step-list semantics, `rippleSteps`, `xorSteps` and the compile lemmas come from
`QuantumComputationDiscoveries.Primitives.Arcsin.Solution` (Copyright 2026 Google LLC,
Apache-2.0). The `OnEncodingBridge` section, `caddcSteps` and the arithmetic helpers are copied
from an unpublished working file of the prime-field multiplication baseline. The modular adder is
copied from an earlier revision of `QuantumSolutions/ModularArithmetic/ModAdd.lean`.
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

/-- Width, modulus and multiplier: `b`-bit register, classical modulus `1 ≤ N ≤ 2^b`, classical
multiplier `a` coprime to `N`. -/
structure ModMulConstParams where
  /-- Register bit-width `b`. -/
  b : ℕ
  /-- Classical modulus `N`. -/
  N : ℕ
  /-- Classical multiplier `a`. -/
  a : ℕ
  /-- The modulus is positive. -/
  hN : 0 < N
  /-- The modulus fits in `b` bits. -/
  hNb : N ≤ 2 ^ b
  /-- The multiplier is invertible modulo `N`. -/
  hcop : Nat.Coprime a N

/-!
## Residue Encoding and the Multiplication Permutation
-/

/-- `b`-bit basis indices below `N`, identified with `Fin N`. -/
def ModMulConstParams.residueEquiv (p : ModMulConstParams) :
    Fin p.N ≃ {x : Fin (2 ^ p.b) // (x : ℕ) < p.N} where
  toFun i := ⟨⟨i, lt_of_lt_of_le i.isLt p.hNb⟩, i.isLt⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Residue map `x ↦ a * x mod N`. -/
def modMulConstFun (p : ModMulConstParams) (x : Fin p.N) : Fin p.N :=
  ⟨p.a * x % p.N, Nat.mod_lt _ p.hN⟩

theorem modMulConstFun_injective (p : ModMulConstParams) :
    Function.Injective (modMulConstFun p) := by
  intro x y h
  have h' : p.a * x ≡ p.a * y [MOD p.N] := congrArg Fin.val h
  have h'' := Nat.ModEq.cancel_left_div_gcd p.hN h'
  rw [Nat.gcd_comm, Nat.Coprime.gcd_eq_one p.hcop, Nat.div_one] at h''
  exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt h'' x.isLt y.isLt)

/-- Basis permutation of the `b`-bit register: `x ↦ a * x mod N` on residues `x < N`, fixing
every `x ≥ N`. Only valid inputs are constrained by the correctness theorem. -/
noncomputable def modMulConstPerm (p : ModMulConstParams) : Equiv.Perm (Fin (2 ^ p.b)) :=
  Equiv.Perm.extendDomain
    (Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (modMulConstFun_injective p)))
    p.residueEquiv

/-- Valid inputs: the register holds a residue, `x < N`. -/
def modMulConstValidInputs (p : ModMulConstParams) : Set (Fin (2 ^ p.b)) :=
  {x | (x : ℕ) < p.N}

/-- On valid inputs, `modMulConstPerm` is `x ↦ a * x mod N`. -/
theorem modMulConstPerm_apply_valid (p : ModMulConstParams) (x : Fin (2 ^ p.b))
    (hx : (x : ℕ) < p.N) :
    ((modMulConstPerm p x : Fin (2 ^ p.b)) : ℕ) = p.a * x % p.N := by
  rw [modMulConstPerm, Equiv.Perm.extendDomain_apply_subtype _ p.residueEquiv (b := x) hx]
  rfl

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive ModMulConst.Var where | v deriving DecidableEq, Inhabited

open ModMulConst (Var)
open ModMulConst.Var (v)

namespace ModMulImpl

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
### Layout inside the combined register

`rAll` is the `2 * b` data wires (`y` at `[0, b)`, `x` at `[b, 2b)`) followed by the `2 * b + 5`
ancilla wires. Source `rX` = `[b, 2b]` (top wire: first ancilla), target `rY` = `[0, b)` plus wire
`2b + 1`, constant register `[2b + 2, 3b + 2]`, carries `[3b + 3, 4b + 2]`, carry-in `4b + 3`,
flag `4b + 4`.
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
### Multiply-accumulate by a constant

`rY ← (rY + c * rD) mod N`: one controlled modular addition of `c * 2^i mod N` per bit `i` of `rD`.
-/

def mulAccSteps (b N c : ℕ) {m : ℕ} (rD : QRegister m n) (rX rY rK : QRegister (b + 1) n)
    (rC : QRegister b n) (ci f : Wire n) : List (Step n) :=
  (List.finRange m).flatMap fun i ↦ cstepSteps b N rX rY rK rC ci f (rD i) (c * 2 ^ (i : ℕ) % N)

theorem runList_mulAcc {b N m : ℕ} {rX rY rK : QRegister (b + 1) n} {rC : QRegister b n}
    {ci f : Wire n} (rD : QRegister m n) (hL : Lay rX rY rK rC ci f)
    (hXK : rX.DisjointWires rK) (hNb : N ≤ 2 ^ b) (hN : 0 < N)
    (hDX : ∀ i, rD i ∉ Set.range rX.wires) (hDY : ∀ i, rD i ∉ Set.range rY.wires)
    (β : BitAssignment n) (hclean : Clean rK rC ci β) (hf : β f = 0) (hX0 : ∀ i, β (rX i) = 0)
    (c y : ℕ) (hy : y < N) :
    runList (mulAccSteps b N c rD rX rY rK rC ci f) (writeReg β rY (natBits (b + 1) y)) =
      some (writeReg β rY (natBits (b + 1) ((y + c * (localIdx rD β : ℕ)) % N))) := by
  have hflat : ∀ (L : List (Fin m)) (u : ℕ), u < N →
      runList (L.flatMap fun i ↦ cstepSteps b N rX rY rK rC ci f (rD i) (c * 2 ^ (i : ℕ) % N))
        (writeReg β rY (natBits (b + 1) u)) =
      some (writeReg β rY (natBits (b + 1)
        ((u + (L.map fun i ↦ (β (rD i)).val * (c * 2 ^ (i : ℕ) % N)).sum) % N))) := by
    intro L
    induction L with
    | nil =>
      intro u hu
      simp only [List.flatMap_nil, List.map_nil, List.sum_nil, add_zero, Nat.mod_eq_of_lt hu,
        runList_nil]
    | cons i L ih =>
      intro u hu
      rw [List.flatMap_cons, runList_append,
        runList_cstep hL hXK hNb (hDX i) (hDY i) β hclean hf hX0 _ u (Nat.mod_lt _ hN) hu,
        Option.bind_some, ih _ (Nat.mod_lt _ hN), List.map_cons, List.sum_cons, Nat.mod_add_mod,
        add_assoc]
  unfold mulAccSteps
  rw [hflat _ y hy]
  refine congrArg some (congrArg (writeReg β rY) (congrArg (natBits (b + 1)) ?_))
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).1
  rw [localIdx_val rD]
  simp only [← Fin.sum_univ_def, Nat.cast_add, Nat.cast_sum, Nat.cast_mul, ZMod.natCast_mod,
    Nat.cast_pow, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

theorem andCount_mulAcc (b N c : ℕ) {m : ℕ} (rD : QRegister m n) (rX rY rK : QRegister (b + 1) n)
    (rC : QRegister b n) (ci f : Wire n) :
    ((mulAccSteps b N c rD rX rY rK rC ci f).map Step.andCount).sum = m * (5 * b) := by
  have hflat : ∀ {α : Type} (L : List α) (F : α → List (Step n)) (k : ℕ),
      (∀ a, ((F a).map Step.andCount).sum = k) →
      (((L.flatMap F).map Step.andCount).sum = L.length * k) := by
    intro α L F k hF
    induction L with
    | nil => simp
    | cons a L ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, hF, ih, List.length_cons]
      ring
  unfold mulAccSteps
  rw [hflat (List.finRange m) _ (5 * b) (fun i ↦ andCount_cstep _ _ _ _ _ _ _ _ _ _),
    List.length_finRange]

/-!
### Swapping two registers with CNOTs
-/

def copySteps : (w : ℕ) → QRegister w n → QRegister w n → List (Step n)
  | 0, _, _ => []
  | w + 1, r, s => Step.cnot (r 0) (s 0) :: copySteps w (regTail r) (regTail s)

theorem runList_copy (w : ℕ) (r s : QRegister w n) (hrs : r.DisjointWires s)
    (β : BitAssignment n) :
    runList (copySteps w r s) β = some (writeReg β s (fun i ↦ β (s i) + β (r i))) := by
  induction w generalizing β with
  | zero =>
    rw [copySteps, runList_nil, show (fun i : Fin 0 ↦ β (s i) + β (r i)) =
      fun i ↦ β (s i) from funext fun i ↦ i.elim0, writeReg_self]
  | succ w ih =>
    have hne : r 0 ≠ s 0 := fun h ↦ not_mem_of_disjoint hrs 0 ⟨0, h.symm⟩
    have htail : (regTail r).DisjointWires (regTail s) := QRegister.disjoint_iff.2 fun i j h ↦ by
      rw [regTail_apply, regTail_apply] at h
      exact not_mem_of_disjoint hrs i.succ ⟨j.succ, h.symm⟩
    have hr0 : ∀ i : Fin w, regTail r i ≠ s 0 := fun i h ↦
      not_mem_of_disjoint hrs i.succ ⟨0, h.symm.trans (regTail_apply r i)⟩
    have hrun : (Step.cnot (r 0) (s 0)).run β = some (update β (s 0) (β (s 0) + β (r 0))) :=
      ite_eq_left hne
    rw [copySteps, runList_cons, hrun, Option.bind_some, ih (regTail r) (regTail s) htail,
      writeReg_succ β s, writeReg_update_of_not_mem _ _ _ (zero_not_mem_regTail s)]
    congr 3
    funext i
    rw [update_of_ne (regTail_ne_zero s i), update_of_ne (hr0 i), regTail_apply, regTail_apply]

theorem andCount_copy (w : ℕ) (r s : QRegister w n) :
    ((copySteps w r s).map Step.andCount).sum = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => rw [copySteps, List.map_cons, List.sum_cons, ih]; rfl

def swapSteps (w : ℕ) (r s : QRegister w n) : List (Step n) :=
  copySteps w r s ++ copySteps w s r ++ copySteps w r s

theorem runList_swap (w : ℕ) (r s : QRegister w n) (hrs : r.DisjointWires s)
    (β : BitAssignment n) :
    runList (swapSteps w r s) β =
      some (writeReg (writeReg β r (fun i ↦ β (s i))) s (fun i ↦ β (r i))) := by
  have hsr : s.DisjointWires r := QRegister.disjoint_comm.1 hrs
  have hrn : ∀ i, r i ∉ Set.range s.wires := fun i ↦ not_mem_of_disjoint hrs i
  have hsn : ∀ i, s i ∉ Set.range r.wires := fun i ↦ not_mem_of_disjoint hsr i
  have e1 : ∀ x y : ZMod 2, x + (y + x) = y := by decide
  have e2 : ∀ x y : ZMod 2, x + y + x = y := by decide
  obtain ⟨β1, hβ1⟩ : ∃ β1, β1 = writeReg β s (fun i ↦ β (s i) + β (r i)) := ⟨_, rfl⟩
  have hA : (fun i ↦ β1 (r i) + β1 (s i)) = fun i ↦ β (s i) := by
    funext i
    rw [hβ1, writeReg_apply_of_not_mem _ _ _ _ (hrn i), writeReg_apply_reg]
    exact e1 _ _
  obtain ⟨β2, hβ2⟩ : ∃ β2, β2 = writeReg β1 r (fun i ↦ β (s i)) := ⟨_, rfl⟩
  have hB : (fun i ↦ β2 (s i) + β2 (r i)) = fun i ↦ β (r i) := by
    funext i
    rw [hβ2, writeReg_apply_of_not_mem _ _ _ _ (hsn i), writeReg_apply_reg, hβ1,
      writeReg_apply_reg]
    exact e2 _ _
  unfold swapSteps
  rw [runList_append, runList_append, runList_copy w r s hrs, ← hβ1, Option.bind_some,
    runList_copy w s r hsr, hA, ← hβ2, Option.bind_some, runList_copy w r s hrs, hB, hβ2, hβ1,
    writeReg_comm _ _ _ hsr, writeReg_writeReg]

theorem andCount_swap (w : ℕ) (r s : QRegister w n) :
    ((swapSteps w r s).map Step.andCount).sum = 0 := by
  simp only [swapSteps, List.map_append, List.sum_append, andCount_copy]

theorem writeReg_congr_reg {k : ℕ} (β : BitAssignment n) {r s : QRegister k n}
    (h : ∀ i, r i = s i) (γ : BitAssignment k) : writeReg β r γ = writeReg β s γ := by
  funext w
  by_cases hw : w ∈ Set.range s.wires
  · obtain ⟨i, rfl⟩ := hw
    have e := writeReg_apply_reg β r γ i
    rw [h i] at e
    rw [e, writeReg_apply_reg]
  · have hw' : w ∉ Set.range r.wires := fun ⟨i, hi⟩ ↦ hw ⟨i, (h i).symm.trans hi⟩
    rw [writeReg_apply_of_not_mem _ _ _ _ hw, writeReg_apply_of_not_mem _ _ _ _ hw']

/-!
### Layout inside the combined register

`rAll` is the `b` data wires `x` followed by the `4 * b + 5` ancilla wires: the accumulator
`[b, 2b]` (its low `b` wires are swapped with `x`), the loaded constant `[2b + 1, 3b + 1]`, the
adder constant register `[3b + 2, 4b + 2]`, the carries `[4b + 3, 5b + 2]`, carry-in `5b + 3`,
flag `5b + 4`.
-/

def gD (b : ℕ) (i : Fin b) : Fin (b + (4 * b + 5)) :=
  ⟨i, by have := i.isLt; omega⟩
def gY (b : ℕ) (i : Fin (b + 1)) : Fin (b + (4 * b + 5)) :=
  ⟨b + i, by have := i.isLt; omega⟩
def gYl (b : ℕ) (i : Fin b) : Fin (b + (4 * b + 5)) :=
  ⟨b + i, by have := i.isLt; omega⟩
def gX (b : ℕ) (i : Fin (b + 1)) : Fin (b + (4 * b + 5)) :=
  ⟨2 * b + 1 + i, by have := i.isLt; omega⟩
def gK (b : ℕ) (i : Fin (b + 1)) : Fin (b + (4 * b + 5)) :=
  ⟨3 * b + 2 + i, by have := i.isLt; omega⟩
def gC (b : ℕ) (i : Fin b) : Fin (b + (4 * b + 5)) :=
  ⟨4 * b + 3 + i, by have := i.isLt; omega⟩

theorem gD_inj (b : ℕ) : Injective (gD b) := fun i j h ↦
  Fin.ext (by have h' := congrArg Fin.val h; simp only [gD] at h'; omega)
theorem gY_inj (b : ℕ) : Injective (gY b) := fun i j h ↦
  Fin.ext (by have h' := congrArg Fin.val h; simp only [gY] at h'; omega)
theorem gYl_inj (b : ℕ) : Injective (gYl b) := fun i j h ↦
  Fin.ext (by have h' := congrArg Fin.val h; simp only [gYl] at h'; omega)
theorem gX_inj (b : ℕ) : Injective (gX b) := fun i j h ↦
  Fin.ext (by have h' := congrArg Fin.val h; simp only [gX] at h'; omega)
theorem gK_inj (b : ℕ) : Injective (gK b) := fun i j h ↦
  Fin.ext (by have h' := congrArg Fin.val h; simp only [gK] at h'; omega)
theorem gC_inj (b : ℕ) : Injective (gC b) := fun i j h ↦
  Fin.ext (by have h' := congrArg Fin.val h; simp only [gC] at h'; omega)

section Layout

variable {b : ℕ} (rAll : QRegister (b + (4 * b + 5)) n)

def regD : QRegister b n := subReg rAll (gD b) (gD_inj b)
def regY : QRegister (b + 1) n := subReg rAll (gY b) (gY_inj b)
def regYl : QRegister b n := subReg rAll (gYl b) (gYl_inj b)
def regX : QRegister (b + 1) n := subReg rAll (gX b) (gX_inj b)
def regK : QRegister (b + 1) n := subReg rAll (gK b) (gK_inj b)
def regC : QRegister b n := subReg rAll (gC b) (gC_inj b)
def wireCi : Wire n := rAll ⟨5 * b + 3, by omega⟩
def wireF : Wire n := rAll ⟨5 * b + 4, by omega⟩

theorem lay_layout :
    Lay (regX rAll) (regY rAll) (regK rAll) (regC rAll) (wireCi rAll) (wireF rAll) := by
  refine ⟨subReg_disj _ _ _ _ _ ?_, subReg_disj _ _ _ _ _ ?_, subReg_disj _ _ _ _ _ ?_,
    subReg_disj _ _ _ _ _ ?_, subReg_disj _ _ _ _ _ ?_,
    not_mem_subReg _ _ _ _ ?_, not_mem_subReg _ _ _ _ ?_, not_mem_subReg _ _ _ _ ?_,
    not_mem_subReg _ _ _ _ ?_, not_mem_subReg _ _ _ _ ?_, not_mem_subReg _ _ _ _ ?_,
    not_mem_subReg _ _ _ _ ?_, not_mem_subReg _ _ _ _ ?_, ?_⟩
  all_goals first
    | (intro i j; have := i.isLt; have := j.isLt; simp only [gX, gY, gK, gC]; omega)
    | (intro i; have := i.isLt; simp only [gX, gY, gK, gC]; omega)
    | (intro h; have h' := congrArg Fin.val (rAll.wires.injective h); simp at h')
    | (intro h; have h' := congrArg Fin.val (rAll.wires.injective h); simp only [] at h'; omega)

theorem lay_extra :
    (regX rAll).DisjointWires (regK rAll) ∧ (regD rAll).DisjointWires (regX rAll) ∧
      (regD rAll).DisjointWires (regY rAll) ∧ (regD rAll).DisjointWires (regYl rAll) := by
  refine ⟨subReg_disj _ _ _ _ _ ?_, subReg_disj _ _ _ _ _ ?_, subReg_disj _ _ _ _ _ ?_,
    subReg_disj _ _ _ _ _ ?_⟩
  all_goals (intro i j; have := i.isLt; have := j.isLt; simp only [gD, gX, gY, gYl, gK]; omega)

end Layout

/-- `x ↦ a * x mod N` in place: multiply-accumulate `a * x` into the zero accumulator, swap it with
`x`, then multiply-accumulate `a' * (a * x mod N)` with `a' = -a⁻¹ mod N`, which clears the
accumulator. -/
def modMulProgSteps (b N a a' : ℕ) (rAll : QRegister (b + (4 * b + 5)) n) : List (Step n) :=
  mulAccSteps b N a (regD rAll) (regX rAll) (regY rAll) (regK rAll) (regC rAll) (wireCi rAll)
    (wireF rAll) ++
  swapSteps b (regD rAll) (regYl rAll) ++
  mulAccSteps b N a' (regD rAll) (regX rAll) (regY rAll) (regK rAll) (regC rAll) (wireCi rAll)
    (wireF rAll)

theorem andCount_modMulProg (b N a a' : ℕ) (rAll : QRegister (b + (4 * b + 5)) n) :
    ((modMulProgSteps b N a a' rAll).map Step.andCount).sum = 10 * (b * b) := by
  unfold modMulProgSteps
  rw [List.map_append, List.map_append, List.sum_append, List.sum_append, andCount_mulAcc,
    andCount_mulAcc, andCount_swap]
  ring

/-- On data `x < N` with zero ancillas, the placed program writes `a * x mod N` into the data
register, given that `a'` undoes `a`. -/
theorem run_modMulProg (b N a a' : ℕ) (hN : 0 < N) (hNb : N ≤ 2 ^ b)
    (rData : QRegister b n) (rAnc : QRegister (4 * b + 5) n)
    (hdisj : rData.DisjointWires rAnc) (β : BitAssignment n) (hanc : localIdx rAnc β = 0)
    (x : ℕ) (hxN : x < N) (hLval : (localIdx rData β : ℕ) = x)
    (hinv : (x + a' * (a * x % N)) % N = 0)
    (J : Fin (2 ^ b)) (hJ : (J : ℕ) = a * x % N) :
    runList (modMulProgSteps b N a a' (rData.concat rAnc hdisj)) β =
      some (writeReg β rData (basisBits b J)) := by
  obtain ⟨rAll, hrAll⟩ : ∃ r, r = rData.concat rAnc hdisj := ⟨_, rfl⟩
  rw [← hrAll]
  have hL : ∀ i : Fin b, rAll (Fin.castAdd (4 * b + 5) i) = rData i := fun i ↦ by
    rw [hrAll]; exact QRegister.concat_apply_left rData rAnc hdisj i
  have hR : ∀ i : Fin (4 * b + 5), rAll (Fin.natAdd b i) = rAnc i := fun i ↦ by
    rw [hrAll]; exact QRegister.concat_apply_right rData rAnc hdisj i
  have hanc0 : ∀ (k : ℕ) (hk : b ≤ k) (hk' : k < b + (4 * b + 5)),
      β (rAll ⟨k, hk'⟩) = 0 := fun k hk hk' ↦ by
    have hk2 : (⟨k, hk'⟩ : Fin (b + (4 * b + 5))) =
        Fin.natAdd b ⟨k - b, by omega⟩ := Fin.ext (by
      show k = b + (k - b)
      omega)
    rw [hk2, hR]
    exact anc_bits_zero rAnc β hanc _
  have hDdat : ∀ i, regD rAll i = rData i := fun i ↦ hL i
  have hxb : x < 2 ^ b := lt_of_lt_of_le hxN hNb
  obtain ⟨r, hr⟩ : ∃ r, r = a * x % N := ⟨_, rfl⟩
  have hrb : r < 2 ^ b := by rw [hr]; exact lt_of_lt_of_le (Nat.mod_lt _ hN) hNb
  have hinv' : (x + a' * r) % N = 0 := by rw [hr]; exact hinv
  have hlay := lay_layout rAll
  obtain ⟨hXK, hDX_d, hDY_d, hDYl⟩ := lay_extra rAll
  have hDX : ∀ i, regD rAll i ∉ Set.range (regX rAll).wires := fun i ↦ not_mem_of_disjoint hDX_d i
  have hDY : ∀ i, regD rAll i ∉ Set.range (regY rAll).wires := fun i ↦ not_mem_of_disjoint hDY_d i
  have hDnYl : ∀ i, regD rAll i ∉ Set.range (regYl rAll).wires := fun i ↦
    not_mem_of_disjoint hDYl i
  have hYnD : ∀ j, regY rAll j ∉ Set.range (regD rAll).wires := fun j ↦
    not_mem_of_disjoint (QRegister.disjoint_comm.1 hDY_d) j
  have hYlast : regY rAll (Fin.last b) ∉ Set.range (regYl rAll).wires := fun ⟨j, hj⟩ ↦
    (Fin.castSucc_lt_last j).ne ((regY rAll).wires.injective
      (show regY rAll (Fin.castSucc j) = regY rAll (Fin.last b) from hj))
  have hbit : ∀ i : Fin b, β (regD rAll i) = ((x / 2 ^ (i : ℕ) % 2 : ℕ) : ZMod 2) := fun i ↦ by
    have h : basisBits b (localIdx rData β) i = β (rData i) := by
      rw [localIdx, Equiv.apply_symm_apply]
    rw [hDdat, ← h, basisBits_eq_div_mod, hLval]
  have hDidx : (localIdx (regD rAll) β : ℕ) = x := by
    rw [← hLval]
    show ((basisBits b).symm (fun i ↦ β (regD rAll i)) : ℕ) =
      ((basisBits b).symm (fun i ↦ β (rData i)) : ℕ)
    rw [show (fun i ↦ β (regD rAll i)) = fun i ↦ β (rData i) from
      funext fun i ↦ by rw [hDdat]]
  -- facts about any state that is zero on the ancillas
  have hstart : ∀ γ : BitAssignment n, (∀ i, γ (regY rAll i) = 0) →
      γ = writeReg γ (regY rAll) (natBits (b + 1) 0) := by
    intro γ hγ
    have h0 : natBits (b + 1) 0 = fun i ↦ γ (regY rAll i) := funext fun i ↦ by
      rw [hγ i]; simp [natBits]
    rw [h0, writeReg_self]
  -- pass 1 from `β`
  have hclean : Clean (regK rAll) (regC rAll) (wireCi rAll) β :=
    ⟨fun i ↦ hanc0 (3 * b + 2 + i) (by omega) (by have := i.isLt; omega),
     fun i ↦ hanc0 (4 * b + 3 + i) (by omega) (by have := i.isLt; omega),
     hanc0 (5 * b + 3) (by omega) (by omega)⟩
  have hf : β (wireF rAll) = 0 := hanc0 (5 * b + 4) (by omega) (by omega)
  have hX0 : ∀ i, β (regX rAll i) = 0 := fun i ↦
    hanc0 (2 * b + 1 + i) (by omega) (by have := i.isLt; omega)
  have hY0 : ∀ i, β (regY rAll i) = 0 := fun i ↦
    hanc0 (b + i) (by omega) (by have := i.isLt; omega)
  obtain ⟨β1, hβ1⟩ : ∃ β1, β1 = writeReg β (regY rAll) (natBits (b + 1) r) := ⟨_, rfl⟩
  have h1 := runList_mulAcc (regD rAll) hlay hXK hNb hN hDX hDY β hclean hf hX0 a 0 hN
  rw [← hstart β hY0, zero_add, hDidx, ← hr, ← hβ1] at h1
  -- the swap
  obtain ⟨β', hβ'⟩ : ∃ β', β' = writeReg β (regD rAll) (natBits b r) := ⟨_, rfl⟩
  have hswap : writeReg (writeReg β1 (regD rAll) (fun i ↦ β1 (regYl rAll i))) (regYl rAll)
      (fun i ↦ β1 (regD rAll i)) = writeReg β' (regY rAll) (natBits (b + 1) x) := by
    funext q
    by_cases hqY : q ∈ Set.range (regY rAll).wires
    · obtain ⟨j, rfl⟩ := hqY
      rw [show writeReg β' (regY rAll) (natBits (b + 1) x) (regY rAll j) = natBits (b + 1) x j
        from writeReg_apply_reg _ _ _ _]
      cases j using Fin.lastCases with
      | last =>
        rw [writeReg_apply_of_not_mem _ _ _ _ hYlast, writeReg_apply_of_not_mem _ _ _ _ (hYnD _),
          hβ1, writeReg_apply_reg]
        simp only [natBits, Fin.val_last, Nat.div_eq_of_lt hrb, Nat.div_eq_of_lt hxb]
      | cast j =>
        have e1 : regY rAll (Fin.castSucc j) = regYl rAll j := rfl
        rw [e1, writeReg_apply_reg]
        show β1 (regD rAll j) = natBits (b + 1) x (Fin.castSucc j)
        rw [hβ1, writeReg_apply_of_not_mem _ _ _ _ (hDY j), hbit j]
        rfl
    · rw [writeReg_apply_of_not_mem _ _ _ _ hqY]
      by_cases hqD : q ∈ Set.range (regD rAll).wires
      · obtain ⟨i, rfl⟩ := hqD
        rw [writeReg_apply_of_not_mem _ _ _ _ (hDnYl i), writeReg_apply_reg]
        show β1 (regYl rAll i) = β' (regD rAll i)
        rw [hβ1, hβ', writeReg_apply_reg]
        exact writeReg_apply_reg β (regY rAll) (natBits (b + 1) r) (Fin.castSucc i)
      · have hqYl : q ∉ Set.range (regYl rAll).wires := fun ⟨j, hj⟩ ↦
          hqY ⟨Fin.castSucc j, hj⟩
        rw [writeReg_apply_of_not_mem _ _ _ _ hqYl, writeReg_apply_of_not_mem _ _ _ _ hqD, hβ1,
          hβ', writeReg_apply_of_not_mem _ _ _ _ hqY, writeReg_apply_of_not_mem _ _ _ _ hqD]
  -- pass 2 from `β'`
  have hnD : ∀ (k : ℕ) (hk : b ≤ k) (hk' : k < b + (4 * b + 5)),
      rAll ⟨k, hk'⟩ ∉ Set.range (regD rAll).wires := fun k hk hk' ↦
    not_mem_subReg rAll (gD b) (gD_inj b) _ fun i ↦ by have := i.isLt; simp only [gD]; omega
  have hanc0' : ∀ (k : ℕ) (hk : b ≤ k) (hk' : k < b + (4 * b + 5)),
      β' (rAll ⟨k, hk'⟩) = 0 := fun k hk hk' ↦ by
    rw [hβ', writeReg_apply_of_not_mem _ _ _ _ (hnD k hk hk')]
    exact hanc0 k hk hk'
  have hclean' : Clean (regK rAll) (regC rAll) (wireCi rAll) β' :=
    ⟨fun i ↦ hanc0' (3 * b + 2 + i) (by omega) (by have := i.isLt; omega),
     fun i ↦ hanc0' (4 * b + 3 + i) (by omega) (by have := i.isLt; omega),
     hanc0' (5 * b + 3) (by omega) (by omega)⟩
  have hf' : β' (wireF rAll) = 0 := hanc0' (5 * b + 4) (by omega) (by omega)
  have hX0' : ∀ i, β' (regX rAll i) = 0 := fun i ↦
    hanc0' (2 * b + 1 + i) (by omega) (by have := i.isLt; omega)
  have hY0' : ∀ i, β' (regY rAll i) = 0 := fun i ↦
    hanc0' (b + i) (by omega) (by have := i.isLt; omega)
  have hDidx' : (localIdx (regD rAll) β' : ℕ) = r := by
    rw [hβ', localIdx_writeReg, ← basisBits_mk_eq_natBits _ _ hrb]
    simp
  have h2 := runList_mulAcc (regD rAll) hlay hXK hNb hN hDX hDY β' hclean' hf' hX0' a' x hxN
  rw [hDidx', hinv', ← hstart β' hY0'] at h2
  have hJbits : basisBits b J = natBits b r := by
    rw [show J = ⟨r, hrb⟩ from Fin.ext (hJ.trans hr.symm), basisBits_mk_eq_natBits]
  unfold modMulProgSteps
  rw [runList_append, runList_append, h1, Option.bind_some, runList_swap b _ _ hDYl,
    Option.bind_some, hswap, h2, hβ', hJbits, writeReg_congr_reg β hDdat]

end ModMulImpl

open ModMulImpl ArcsinImpl OnEncodingBridge

/-- The inverse multiplier used to clear the accumulator: `-a⁻¹ mod N`. -/
def ModMulImpl.aInv (p : ModMulConstParams) : ℕ := (-((p.a : ZMod p.N)⁻¹)).val

theorem ModMulImpl.aInv_spec (p : ModMulConstParams) (x : ℕ) :
    (x + aInv p * (p.a * x % p.N)) % p.N = 0 := by
  have : NeZero p.N := ⟨p.hN.ne'⟩
  have hu : (p.a : ZMod p.N) * (p.a : ZMod p.N)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one p.a p.hcop
  have e1 : ((aInv p : ℕ) : ZMod p.N) = -((p.a : ZMod p.N)⁻¹) := by
    unfold aInv
    exact ZMod.natCast_zmod_val _
  have e2 : ((p.a * x % p.N : ℕ) : ZMod p.N) = (p.a : ZMod p.N) * x := by
    rw [ZMod.natCast_mod, Nat.cast_mul]
  have h0 : ((x + aInv p * (p.a * x % p.N) : ℕ) : ZMod p.N) = ((0 : ℕ) : ZMod p.N) := by
    rw [Nat.cast_add, Nat.cast_mul, e1, e2, Nat.cast_zero]
    calc (x : ZMod p.N) + -((p.a : ZMod p.N)⁻¹) * ((p.a : ZMod p.N) * x)
        = x - x * ((p.a : ZMod p.N) * (p.a : ZMod p.N)⁻¹) := by ring
      _ = 0 := by rw [hu]; ring
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h0
  rwa [Nat.zero_mod] at this

theorem ModMulImpl.run_modMulProg' {n : ℕ} (p : ModMulConstParams) (rData : QRegister p.b n)
    (rAnc : QRegister (4 * p.b + 5) n) (hdisj : rData.DisjointWires rAnc) (β : BitAssignment n)
    (hanc : localIdx rAnc β = 0) (hv : localIdx rData β ∈ modMulConstValidInputs p) :
    runList (modMulProgSteps p.b p.N p.a (aInv p) (rData.concat rAnc hdisj)) β =
      some (writeReg β rData (basisBits p.b (modMulConstPerm p (localIdx rData β)))) :=
  run_modMulProg p.b p.N p.a (aInv p) p.hN p.hNb rData rAnc hdisj β hanc _ hv rfl
    (aInv_spec p _) _ (modMulConstPerm_apply_valid p _ hv)

open ArcsinImpl OnEncodingBridge


/-- Number of clean ancilla qubits `modMulConstProgram` uses for parameters `p`. -/
def modMulConstAncillas (p : ModMulConstParams) : ℕ := 4 * p.b + 5

/-- Parameterized circuit on `p.b` data wires `rData` (little-endian `x`) and
`modMulConstAncillas p` clean ancilla wires `rAnc`. -/
def modMulConstProgram {n : ℕ} (p : ModMulConstParams)
    (rData : QRegister p.b n)
    (rAnc : QRegister (modMulConstAncillas p) n) : DynamicCircuit Var n :=
  if h : ∀ i j, rData i ≠ rAnc j then
    compileList v (modMulProgSteps p.b p.N p.a (ModMulImpl.aInv p)
      (rData.concat rAnc (QRegister.disjoint_iff.2 h)))
  else .identity

/-- Parameterized correctness theorem: for every width, modulus `1 ≤ N ≤ 2^b` and multiplier
`a` coprime to `N`, `modMulConstProgram p` maps every valid input `|x⟩` (`x < N`) with clean
ancillas to `|a * x mod N⟩` with clean ancillas, across all disjoint register placements. -/
theorem modMulConst_correctness (p : ModMulConstParams) :
    ∀ {n : ℕ}
      (rData : QRegister p.b n)
      (rAnc : QRegister (modMulConstAncillas p) n)
      (hdisj : rData.DisjointWires rAnc),
      RealizesCleanSubroutineOnEncoding rData rAnc hdisj (modMulConstValidInputs p)
        (modMulConstPerm p) (modMulConstProgram p rData rAnc).compile := by
  intro n rData rAnc hdisj
  have h : ∀ i j, rData i ≠ rAnc j := QRegister.disjoint_iff.1 hdisj
  have hprog : modMulConstProgram p rData rAnc =
      compileList v (modMulProgSteps p.b p.N p.a (ModMulImpl.aInv p)
        (rData.concat rAnc hdisj)) := by
    rw [modMulConstProgram, dite_eq_left h]
  rw [hprog]
  obtain ⟨R, hK, hR, -⟩ := exists_lowerKraus_compileList v
    (modMulProgSteps p.b p.N p.a (ModMulImpl.aInv p) (rData.concat rAnc hdisj))
  exact realizesCleanSubroutineOnEncoding_of_lowerKraus rData rAnc hdisj _ _ hK
    fun β hβ hv ↦ hR β _ (ModMulImpl.run_modMulProg' p rData rAnc hdisj β hβ hv)


/-- `T`-gate count of `modMulConstProgram p`. -/
abbrev modMulConstTCount {n : ℕ} (p : ModMulConstParams)
    (rData : QRegister p.b n)
    (rAnc : QRegister (modMulConstAncillas p) n) : ℕ :=
  (modMulConstProgram p rData rAnc).count PrimitiveGate.T

/-- Spacetime cost `T count * qubits` of `modMulConstProgram p`, counting all
`p.b + modMulConstAncillas p` data and clean ancilla qubits. -/
abbrev modMulConstSpacetime {n : ℕ} (p : ModMulConstParams)
    (rData : QRegister p.b n)
    (rAnc : QRegister (modMulConstAncillas p) n) : ℕ :=
  modMulConstTCount p rData rAnc * (p.b + modMulConstAncillas p)

/-!
## Cost Theorems

Both forbid primitive `TOFF` gates and hold uniformly over every modulus and every coprime
multiplier at width `b = 2048`.
-/

/-- At width `b`, for every modulus and coprime multiplier, `modMulConstProgram` uses no
primitive `TOFF` gates and has spacetime cost at most `cost` across all register placements. -/
abbrev SatisfiesModMulConstSpacetimeBound (b cost : ℕ) : Prop :=
  ∀ (p : ModMulConstParams), p.b = b →
    ∀ {n : ℕ}
      (rData : QRegister p.b n)
      (rAnc : QRegister (modMulConstAncillas p) n),
      (modMulConstProgram p rData rAnc).count PrimitiveGate.TOFF = 0 ∧
        modMulConstSpacetime p rData rAnc ≤ cost

/-- At width `b`, for every modulus and coprime multiplier, `modMulConstProgram` uses no
primitive `TOFF` gates and at most `cost` `T` gates across all register placements. -/
abbrev SatisfiesModMulConstTCountBound (b cost : ℕ) : Prop :=
  ∀ (p : ModMulConstParams), p.b = b →
    ∀ {n : ℕ}
      (rData : QRegister p.b n)
      (rAnc : QRegister (modMulConstAncillas p) n),
      (modMulConstProgram p rData rAnc).count PrimitiveGate.TOFF = 0 ∧
        modMulConstTCount p rData rAnc ≤ cost

theorem ModMulImpl.modMulConstProgram_count {n : ℕ} (p : ModMulConstParams)
    (rData : QRegister p.b n) (rAnc : QRegister (modMulConstAncillas p) n) :
    (modMulConstProgram p rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (modMulConstProgram p rData rAnc).count PrimitiveGate.T ≤ 4 * (10 * (p.b * p.b)) := by
  by_cases h : ∀ i j, rData i ≠ rAnc j
  · rw [modMulConstProgram, dite_eq_left h]
    refine ⟨count_TOFF_compileList _ _, (count_T_compileList _ _).trans ?_⟩
    rw [andCount_modMulProg]
  · rw [modMulConstProgram, dite_eq_right h]
    exact ⟨rfl, Nat.zero_le _⟩

/-- Claimed spacetime cost bound at `b = 2048`. -/
def modMulConstB2048SpacetimeCost : ℕ := 1718825779200

theorem modMulConst_b2048_spacetime_cost :
    SatisfiesModMulConstSpacetimeBound 2048 modMulConstB2048SpacetimeCost := by
  intro p hp n rData rAnc
  obtain ⟨h0, hT⟩ := ModMulImpl.modMulConstProgram_count p rData rAnc
  refine ⟨h0, ?_⟩
  calc modMulConstSpacetime p rData rAnc ≤
        4 * (10 * (p.b * p.b)) * (p.b + modMulConstAncillas p) :=
        Nat.mul_le_mul_right _ hT
    _ = modMulConstB2048SpacetimeCost := by rw [modMulConstAncillas, hp]; rfl

/-- Claimed `T`-count bound at `b = 2048`. -/
def modMulConstB2048TCountCost : ℕ := 167772160

theorem modMulConst_b2048_t_count_cost :
    SatisfiesModMulConstTCountBound 2048 modMulConstB2048TCountCost := by
  intro p hp n rData rAnc
  obtain ⟨h0, hT⟩ := ModMulImpl.modMulConstProgram_count p rData rAnc
  refine ⟨h0, hT.trans ?_⟩
  rw [hp]
  decide

end QuantumComputation.Specs
