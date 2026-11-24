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

/-!
# Controlled Addition of a Classical Constant (`controlledAddConstant`) Specification: Baseline Solution

Baseline: write the constant `a` into `k` clean ancilla wires with `X` gates controlled on the
control wire (`CNOT`), add those wires into the target with the ripple-carry adder
`ArcsinImpl.rippleSteps` (temporary-AND carries, measurement based uncomputation), then erase the
constant with the same controlled writes. With the control at `0` the clean wires stay zero and the
adder adds zero. It uses `2 * k` clean ancillas and at most `4 * (k - 1)` `T` gates. The
specification text below is unchanged; only the holes are filled and the theorems proved.

Parameterized specification for reversible in-place addition of a classical constant to a `k`-bit
quantum register controlled on one qubit, `|c⟩|y⟩|0⟩^⊗m ↦ |c⟩|(y + c * a) mod 2^k⟩|0⟩^⊗m`, for every
bit-width `k` and every constant `a` in `[0, 2^k)`. The register holds an unsigned integer,
least-significant bit first. The control `c` is preserved and the `m` clean ancilla qubits are
returned to zero. The constant is known when the circuit is built, so the program may depend on `a`;
the ancilla count and both claimed costs depend only on `k` and must hold for the worst constant.
Kets are written with the most significant register on the left, so the rightmost register occupies
the lowest wires.

There are two resource metrics over Clifford + `T` with measurements: the `T` count, and spacetime
(`T count * qubits`), where `qubits = 1 + k + controlledAddConstantAncillas k` is the total number
of data and clean ancilla qubits. Each metric has three cost theorems. One bounds the cost at every
bit-width `k` and every constant `a` by a claimed function of `k`. The other two pin the bit-widths
`k = 64` and `k = 2048` and bound the cost by a claimed closed constant, so that two solutions can
be compared by a number. `TOFF` gates are excluded, so each Toffoli is costed by its Clifford + `T`
construction, such as `4` `T` gates with an ancilla and a measurement (C. Jones, Phys. Rev. A 87,
022328 (2013)).

References for the textbook constructions:
* C. Gidney, "Halving the cost of quantum addition", Quantum 2, 74 (2018), arXiv:1709.06648.
* T. Haener, M. Roetteler, K. M. Svore, "Factoring using 2n+2 qubits with Toffoli based modular
  multiplication", arXiv:1611.07995 (addition of a classical constant with few ancillas).
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator

/-!
## Reversible Controlled Constant-Addition Unitary
-/

/-- The controlled constant `c * a` as a table on the one-qubit control index `c`. -/
def controlledConstant {k : ℕ} (a : Fin (2 ^ k)) (c : Fin (2 ^ 1)) : Fin (2 ^ k) :=
  if c = 1 then a else 0

/-- Ideal `(1 + k)`-qubit unitary `|c⟩|y⟩ ↦ |c⟩|(y + c * a) mod 2^k⟩`: the basis permutation
`tableAddPerm` of `controlledConstant a`, with the target `y` as the low `k` bits of the basis index
and the control `c` as the highest bit. -/
noncomputable abbrev controlledAddConstantUnitary (k : ℕ) (a : Fin (2 ^ k)) :
    Unitary (2 ^ (1 + k)) :=
  permutationUnitary (tableAddPerm (controlledConstant a))

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive ControlledAddConstant.Var where | v deriving DecidableEq, Inhabited

open ControlledAddConstant (Var)
open ControlledAddConstant.Var (v)

/-!
## Baseline Construction
-/

namespace ControlledAddConstantImpl

open ArcsinImpl ArcsinImpl.Step

variable {n : ℕ}

/-- Value of `tableAddPerm f` on a basis index with low part `b` and high part `x`. Same proof as
`equalTableAddPerm_val_of_eq` in the `arcsin` solution (`StageProofB`), for unequal widths. -/
theorem tableAddPerm_val {m k : ℕ} (f : Fin (2 ^ m) → Fin (2 ^ k))
    (j : Fin (2 ^ (m + k))) (b : Fin (2 ^ k)) (x : Fin (2 ^ m))
    (hb : j.val % 2 ^ k = b.val) (hx : j.val / 2 ^ k = x.val) :
    ((tableAddPerm f) j : ℕ) = (b.val + (f x).val) % 2 ^ k + 2 ^ k * x.val := by
  have hjx : (Fin.cast (by rw [pow_add]) j).divNat = x :=
    Fin.ext (by simp [Fin.divNat, hx])
  simp [tableAddPerm, splitBasisEquiv, addRightShear, finProdFinEquiv_symm_apply, hjx,
    Fin.modNat, hb, Fin.val_add]

theorem controlledConstant_val {k : ℕ} (a : Fin (2 ^ k)) (x : Fin (2 ^ 1)) :
    (controlledConstant a x : ℕ) = if x.val = 1 then a.val else 0 := by
  have hone : ((1 : Fin (2 ^ 1)) : ℕ) = 1 := rfl
  unfold controlledConstant
  by_cases h : x = 1
  · subst h
    simp
  · have h' : x.val ≠ 1 := fun h' ↦ h (Fin.ext (by rw [h', hone]))
    simp [h, h']

/-- Value of the ideal permutation `tableAddPerm (controlledConstant a)` on a basis index. -/
theorem tableAddPerm_controlledConstant_val {k : ℕ} (a : Fin (2 ^ k)) (j : Fin (2 ^ (1 + k))) :
    ((tableAddPerm (controlledConstant a) j : Fin (2 ^ (1 + k))) : ℕ) =
      ((j : ℕ) % 2 ^ k + if (j : ℕ) / 2 ^ k = 1 then a.val else 0) % 2 ^ k +
        2 ^ k * ((j : ℕ) / 2 ^ k) := by
  have hdiv_lt : (j : ℕ) / 2 ^ k < 2 ^ 1 :=
    Nat.div_lt_of_lt_mul (lt_of_lt_of_eq j.isLt (by rw [pow_add]; exact Nat.mul_comm _ _))
  have h := tableAddPerm_val (controlledConstant a) j
    ⟨(j : ℕ) % 2 ^ k, Nat.mod_lt _ (by positivity)⟩ ⟨(j : ℕ) / 2 ^ k, hdiv_lt⟩ rfl rfl
  rw [controlledConstant_val] at h
  exact h

/-- Controlled on the wire `rData k`: write the constant `a` into the clean wires `rAnc[0, k)`,
ripple-add them into the target `rData[0, k)` with carry-in wire `rAnc k` and carry wires
`rAnc[k + 1, 2 k)`, then erase the constant again. -/
def controlledAddConstantSteps :
    (k : ℕ) → Fin (2 ^ k) → QRegister (1 + k) n → QRegister (2 * k) n → List (Step n)
  | 0, _, _, _ => []
  | K + 1, a, rData, rAnc =>
      xorSteps (some (rData ⟨K + 1, by omega⟩)) (K + 1) (rAnc.slice 0 (K + 1) (by omega))
          (basisBits (K + 1) a) ++
        rippleSteps K (rAnc.slice 0 (K + 1) (by omega)) (rData.slice 0 (K + 1) (by omega))
          (rAnc ⟨K + 1, by omega⟩) (rAnc.slice (K + 2) K (by omega)) ++
        xorSteps (some (rData ⟨K + 1, by omega⟩)) (K + 1) (rAnc.slice 0 (K + 1) (by omega))
          (basisBits (K + 1) a)

theorem andCount_controlledAddConstantSteps (k : ℕ) (a : Fin (2 ^ k)) (rData : QRegister (1 + k) n)
    (rAnc : QRegister (2 * k) n) :
    ((controlledAddConstantSteps k a rData rAnc).map Step.andCount).sum = k - 1 := by
  cases k with
  | zero => rfl
  | succ K =>
    rw [controlledAddConstantSteps, List.map_append, List.map_append, List.sum_append,
      List.sum_append, andCount_xorSteps, andCount_rippleSteps]
    omega

/-- Writing `m * d` into the clean wires `rY` and xoring `m * d` again cancels. -/
theorem writeReg_cancel {k : ℕ} (β : BitAssignment n) (rY rB : QRegister k n)
    (hYB : rY.DisjointWires rB) (m : ZMod 2) (d : BitAssignment k) (γ : BitAssignment k)
    (hY : ∀ i, β (rY i) = 0) :
    writeReg (writeReg (writeReg β rY (fun i ↦ m * d i)) rB γ) rY
        (fun i ↦ writeReg (writeReg β rY (fun i ↦ m * d i)) rB γ (rY i) + m * d i) =
      writeReg β rB γ := by
  have h2 : ∀ m x : ZMod 2, m * x + m * x = 0 := by decide
  funext w
  by_cases hw1 : w ∈ Set.range rY.wires
  · obtain ⟨i, rfl⟩ := hw1
    have hi : rY i ∉ Set.range rB.wires := not_mem_of_disjoint hYB i
    simp only [writeReg_apply_reg, writeReg_apply_of_not_mem _ _ _ _ hi, hY i, h2]
  · by_cases hw2 : w ∈ Set.range rB.wires
    · obtain ⟨i, rfl⟩ := hw2
      have hi : rB i ∉ Set.range rY.wires := not_mem_of_disjoint (QRegister.disjoint_comm.mp hYB) i
      simp only [writeReg_apply_of_not_mem _ _ _ _ hi, writeReg_apply_reg]
    · simp only [writeReg_apply_of_not_mem _ _ _ _ hw1, writeReg_apply_of_not_mem _ _ _ _ hw2]

theorem runList_ctrlAddCore (K : ℕ) (c : Option (Wire n)) (d : BitAssignment (K + 1))
    (rY rB : QRegister (K + 1) n) (ci : Wire n) (rC : QRegister K n)
    (hYB : rY.DisjointWires rB) (hYC : rY.DisjointWires rC)
    (hBC : rB.DisjointWires rC) (hA : ci ∉ Set.range rY.wires) (hB : ci ∉ Set.range rB.wires)
    (hC : ci ∉ Set.range rC.wires) (hcY : ∀ i, CtrlNe c (rY i)) (hcB : ∀ i, CtrlNe c (rB i))
    (β : BitAssignment n) (hY : ∀ i, β (rY i) = 0)
    (hci : β ci = 0) (hC0 : ∀ i, β (rC i) = 0) :
    runList (xorSteps c (K + 1) rY d ++ rippleSteps K rY rB ci rC ++
        xorSteps c (K + 1) rY d) β =
      some (writeReg β rB (basisBits (K + 1)
        ⟨((((basisBits (K + 1)).symm (fun i ↦ ctrlVal c β * d i) : Fin (2 ^ (K + 1))) : ℕ) +
            (localIdx rB β : ℕ)) % 2 ^ (K + 1), Nat.mod_lt _ (by positivity)⟩)) := by
  have hd : (fun i ↦ β (rY i) + ctrlVal c β * d i) = fun i ↦ ctrlVal c β * d i :=
    funext fun i ↦ by simp [hY i]
  have h1 : runList (xorSteps c (K + 1) rY d) β =
      some (writeReg β rY (fun i ↦ ctrlVal c β * d i)) := by
    rw [runList_xorSteps c _ _ _ hcY, hd]
  have hC1 : ∀ i, writeReg β rY (fun i ↦ ctrlVal c β * d i) (rC i) = 0 := fun i ↦ by
    rw [writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hYC) i)]
    exact hC0 i
  have hidx : (⟨((localIdx rY (writeReg β rY (fun i ↦ ctrlVal c β * d i)) : ℕ) +
        (localIdx rB (writeReg β rY (fun i ↦ ctrlVal c β * d i)) : ℕ) +
        (writeReg β rY (fun i ↦ ctrlVal c β * d i) ci).val) % 2 ^ (K + 1),
        Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ (K + 1))) =
      ⟨((((basisBits (K + 1)).symm (fun i ↦ ctrlVal c β * d i) : Fin (2 ^ (K + 1))) : ℕ) +
        (localIdx rB β : ℕ)) % 2 ^ (K + 1), Nat.mod_lt _ (by positivity)⟩ := by
    apply Fin.ext
    simp only [localIdx_writeReg, localIdx_writeReg_of_disjoint β rY rB hYB _,
      writeReg_apply_of_not_mem β rY _ ci hA, hci, ZMod.val_zero, add_zero]
  rw [runList_append, runList_append, h1, Option.bind_some,
    runList_rippleSteps K rY rB ci rC hYB hYC hBC hA hB hC _ hC1, Option.bind_some,
    runList_xorSteps c _ _ _ hcY, hidx, ctrlVal_writeReg hcB, ctrlVal_writeReg hcY]
  exact congrArg some (writeReg_cancel β rY rB hYB (ctrlVal c β) d _ hY)

/-- Writing the low `K + 1` wires of `rData` with `g` is writing the whole register with the index
`σ'` whose high part is the untouched control. -/
theorem writeReg_low_eq (K : ℕ) (rData : QRegister (1 + (K + 1)) n) (β : BitAssignment n)
    (g : Fin (2 ^ (K + 1))) (σ' : Fin (2 ^ (1 + (K + 1))))
    (h : (σ' : ℕ) = (g : ℕ) + 2 ^ (K + 1) *
      (localIdx (rData.slice (K + 1) 1 (by omega)) β : ℕ)) :
    writeReg β (rData.slice 0 (K + 1) (by omega)) (basisBits (K + 1) g) =
      writeReg β rData (basisBits (1 + (K + 1)) σ') := by
  have hLH : (rData.slice 0 (K + 1) (by omega)).DisjointWires
      (rData.slice (K + 1) 1 (by omega)) :=
    QRegister.slice_disjoint_of_le rData 0 (K + 1) (K + 1) 1 (by omega) (by omega) (by omega)
  have key : localIdx rData
      (writeReg β (rData.slice 0 (K + 1) (by omega)) (basisBits (K + 1) g)) = σ' := by
    apply Fin.ext
    rw [h, localIdx_val_split rData (K + 1) 1 (by omega), localIdx_writeReg,
      basisBitsEquiv_symm_basisBits, localIdx_writeReg_of_disjoint _ _ _ hLH]
  calc writeReg β (rData.slice 0 (K + 1) (by omega)) (basisBits (K + 1) g)
      = writeReg β rData (fun i ↦
          writeReg β (rData.slice 0 (K + 1) (by omega)) (basisBits (K + 1) g) (rData i)) :=
        (writeReg_eq_of_eqOn β
          (writeReg β (rData.slice 0 (K + 1) (by omega)) (basisBits (K + 1) g)) rData
          fun w hw ↦ writeReg_apply_of_not_mem _ _ _ _ fun ⟨i, h⟩ ↦ hw ⟨_, h⟩).symm
    _ = writeReg β rData (basisBits (1 + (K + 1)) σ') :=
        congrArg (writeReg β rData)
          (by rw [← key]; exact (basisBits_basisBitsEquiv_symm _ _).symm)

theorem runList_controlledAddConstantSteps (k : ℕ) (a : Fin (2 ^ k)) (rData : QRegister (1 + k) n)
    (rAnc : QRegister (2 * k) n) (hdisj : rData.DisjointWires rAnc)
    (σ : Equiv.Perm (Fin (2 ^ (1 + k))))
    (hσ : ∀ j, (σ j : ℕ) =
      ((j : ℕ) % 2 ^ k + if (j : ℕ) / 2 ^ k = 1 then a.val else 0) % 2 ^ k +
        2 ^ k * ((j : ℕ) / 2 ^ k))
    (β : BitAssignment n) (hβ : localIdx rAnc β = 0) :
    runList (controlledAddConstantSteps k a rData rAnc) β =
      some (writeReg β rData (basisBits (1 + k) (σ (localIdx rData β)))) := by
  cases k with
  | zero =>
    have h : σ (localIdx rData β) = localIdx rData β := Fin.ext (by
      rw [hσ]
      simp only [pow_zero, Nat.mod_one, Nat.div_one, one_mul, zero_add])
    rw [controlledAddConstantSteps, runList_nil, h, basisBits_basisBitsEquiv_symm, writeReg_self]
  | succ K =>
    have hclean := eq_zero_of_localIdx_eq_zero rAnc β hβ
    have hDA : ∀ {p q : ℕ} (r : QRegister p (1 + (K + 1))) (r' : QRegister q (2 * (K + 1))),
        (rData.compose r).DisjointWires (rAnc.compose r') := fun _ _ ↦
      (hdisj.compose_left _).compose_right _
    have hcY : ∀ i, CtrlNe (some (rData ⟨K + 1, by omega⟩))
        ((rAnc.slice 0 (K + 1) (by omega)) i) := fun i ↦
      CtrlNe.some fun h ↦ hdisj.ne ⟨K + 1, by omega⟩ ⟨0 + i.val, by omega⟩ h
    have hcB : ∀ i, CtrlNe (some (rData ⟨K + 1, by omega⟩))
        ((rData.slice 0 (K + 1) (by omega)) i) := fun i ↦
      CtrlNe.some fun h ↦ apply_not_mem_slice rData ⟨K + 1, by omega⟩ 0 (K + 1) (by omega)
        (Or.inr (by simp)) ⟨i, h.symm⟩
    rw [controlledAddConstantSteps, runList_ctrlAddCore K _ (basisBits (K + 1) a) _ _ _ _
      (QRegister.disjoint_comm.mp (hDA _ _))
      (QRegister.slice_disjoint_of_le rAnc 0 (K + 1) (K + 2) K (by omega) (by omega) (by omega))
      (hDA _ _) (apply_not_mem_slice rAnc ⟨K + 1, by omega⟩ 0 (K + 1) (by omega)
        (Or.inr (by simp)))
      (fun ⟨i, h⟩ ↦ hdisj.ne ⟨0 + i.val, by omega⟩ ⟨K + 1, by omega⟩ h)
      (apply_not_mem_slice rAnc ⟨K + 1, by omega⟩ (K + 2) K (by omega)
        (Or.inl (by dsimp; omega)))
      hcY hcB β (fun _ ↦ hclean _) (hclean _) (fun _ ↦ hclean _)]
    refine congrArg some (writeReg_low_eq K rData β _ _ ?_)
    have hL := (localIdx (rData.slice 0 (K + 1) (by omega)) β).isLt
    have hv1 : (1 : ZMod 2).val = 1 := rfl
    have hH : (localIdx (rData.slice (K + 1) 1 (by omega)) β : ℕ) =
        (β (rData ⟨K + 1, by omega⟩)).val := by
      have h1 := localIdx_val_succ (rData.slice (K + 1) 1 (by omega)) β
      have h0 := (localIdx (regTail (rData.slice (K + 1) 1 (by omega))) β).isLt
      have e : β ((rData.slice (K + 1) 1 (by omega)) 0) = β (rData ⟨K + 1, by omega⟩) := rfl
      simp only [pow_zero] at h0
      rw [e] at h1
      omega
    have hE : (((basisBits (K + 1)).symm (fun i ↦
          ctrlVal (some (rData ⟨K + 1, by omega⟩)) β * basisBits (K + 1) a i) :
          Fin (2 ^ (K + 1))) : ℕ) =
        if (β (rData ⟨K + 1, by omega⟩)).val = 1 then a.val else 0 := by
      rcases bit_cases (β (rData ⟨K + 1, by omega⟩)) with h0 | h1
      · have e : (fun i ↦ ctrlVal (some (rData ⟨K + 1, by omega⟩)) β * basisBits (K + 1) a i) =
            0 := funext fun i ↦ by simp [ctrlVal, h0]
        rw [e, basisBits_symm_zero, h0]
        simp
      · have e : (fun i ↦ ctrlVal (some (rData ⟨K + 1, by omega⟩)) β * basisBits (K + 1) a i) =
            basisBits (K + 1) a := funext fun i ↦ by simp [ctrlVal, h1]
        rw [e, basisBitsEquiv_symm_basisBits, h1]
        simp [hv1]
    rw [hσ, localIdx_val_split rData (K + 1) 1 (by omega) β, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hL, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hL]
    simp only [zero_add, hH, hE]
    rw [Nat.add_comm (localIdx (rData.slice 0 (K + 1) (by omega)) β : ℕ)]

end ControlledAddConstantImpl

open ArcsinImpl ArcsinImpl.Step

/-- Number of clean ancilla qubits `controlledAddConstantProgram` uses at bit-width `k`. -/
def controlledAddConstantAncillas (k : ℕ) : ℕ := 2 * k

/-- Parameterized controlled constant adder on `1 + k` data wires `rData` (`k` target wires `y`,
least-significant bit first, followed by the control wire `c`) and `controlledAddConstantAncillas k`
clean ancilla wires `rAnc`. -/
def controlledAddConstantProgram {n : ℕ} (k : ℕ) (a : Fin (2 ^ k))
    (rData : QRegister (1 + k) n)
    (rAnc : QRegister (controlledAddConstantAncillas k) n) : DynamicCircuit Var n :=
  compileList v (ControlledAddConstantImpl.controlledAddConstantSteps k a rData rAnc)

/-- Parameterized correctness theorem: for every bit-width `k` and every constant `a : Fin (2 ^ k)`,
`controlledAddConstantProgram k a` realizes `controlledAddConstantUnitary k a` as an exact clean
subroutine across all disjoint register placements. -/
theorem controlled_add_constant_correctness (k : ℕ) (a : Fin (2 ^ k)) :
    ∀ {n : ℕ}
      (rData : QRegister (1 + k) n)
      (rAnc : QRegister (controlledAddConstantAncillas k) n)
      (hdisj : rData.DisjointWires rAnc),
      RealizesCleanSubroutine rData rAnc hdisj (controlledAddConstantUnitary k a)
        (controlledAddConstantProgram k a rData rAnc).compile := by
  intro n rData rAnc hdisj
  exact realizesCleanSubroutine_compileList v _ rData rAnc hdisj
    (tableAddPerm (controlledConstant a)) fun β hβ ↦
    ControlledAddConstantImpl.runList_controlledAddConstantSteps k a rData rAnc hdisj _
      (ControlledAddConstantImpl.tableAddPerm_controlledConstant_val a) β hβ

/-- `T`-gate count of `controlledAddConstantProgram k a`, which the cost predicates require to use
no `TOFF` gates. -/
abbrev controlledAddConstantTCount {n : ℕ} (k : ℕ) (a : Fin (2 ^ k))
    (rData : QRegister (1 + k) n)
    (rAnc : QRegister (controlledAddConstantAncillas k) n) : ℕ :=
  (controlledAddConstantProgram k a rData rAnc).count PrimitiveGate.T

/-- Spacetime cost `T count * qubits` of `controlledAddConstantProgram k a`, counting all
`1 + k + controlledAddConstantAncillas k` data and clean ancilla qubits. -/
abbrev controlledAddConstantSpacetime {n : ℕ} (k : ℕ) (a : Fin (2 ^ k))
    (rData : QRegister (1 + k) n)
    (rAnc : QRegister (controlledAddConstantAncillas k) n) : ℕ :=
  controlledAddConstantTCount k a rData rAnc * (1 + k + controlledAddConstantAncillas k)

/-!
## Cost Predicates

Both predicates forbid primitive `TOFF` gates (so every Toffoli must be decomposed into Clifford +
`T` + measurements) and bound a cost of `controlledAddConstantProgram` at bit-width `k` and every
constant `a : Fin (2 ^ k)` across all register placements.
-/

/-- `controlledAddConstantProgram` at bit-width `k` uses no primitive `TOFF` gates and has `T` count
at most `cost`, for every constant and register placement it can be given. -/
abbrev SatisfiesControlledAddConstantTBound (k cost : ℕ) : Prop :=
  ∀ (a : Fin (2 ^ k)) {n : ℕ}
    (rData : QRegister (1 + k) n)
    (rAnc : QRegister (controlledAddConstantAncillas k) n),
    (controlledAddConstantProgram k a rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      controlledAddConstantTCount k a rData rAnc ≤ cost

/-- `controlledAddConstantProgram` at bit-width `k` uses no primitive `TOFF` gates and has spacetime
cost at most `cost`, for every constant and register placement it can be given. -/
abbrev SatisfiesControlledAddConstantSpacetimeBound (k cost : ℕ) : Prop :=
  ∀ (a : Fin (2 ^ k)) {n : ℕ}
    (rData : QRegister (1 + k) n)
    (rAnc : QRegister (controlledAddConstantAncillas k) n),
    (controlledAddConstantProgram k a rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      controlledAddConstantSpacetime k a rData rAnc ≤ cost

/-- The baseline uses no `TOFF` gates and at most `4 * (k - 1)` `T` gates. -/
theorem controlled_add_constant_baseline_t_bound (k : ℕ) :
    SatisfiesControlledAddConstantTBound k (4 * (k - 1)) := by
  intro a n rData rAnc
  refine ⟨count_TOFF_compileList v _, ?_⟩
  have h := count_T_compileList v
    (ControlledAddConstantImpl.controlledAddConstantSteps k a rData rAnc)
  exact h.trans (le_of_eq (congrArg (4 * ·)
    (ControlledAddConstantImpl.andCount_controlledAddConstantSteps k a rData rAnc)))

/-- The baseline has spacetime cost at most `4 * (k - 1) * (1 + k + 2 * k)`. -/
theorem controlled_add_constant_baseline_spacetime_bound (k : ℕ) :
    SatisfiesControlledAddConstantSpacetimeBound k (4 * (k - 1) * (1 + k + 2 * k)) := by
  intro a n rData rAnc
  exact ⟨(controlled_add_constant_baseline_t_bound k a rData rAnc).1,
    Nat.mul_le_mul_right _ (controlled_add_constant_baseline_t_bound k a rData rAnc).2⟩

/-!
## Cost Theorems at Every Bit-Width
-/

/-- Claimed `T` count of `controlledAddConstantProgram`, as a function of the bit-width `k`. -/
def controlledAddConstantTCost (k : ℕ) : ℕ := 4 * (k - 1)

theorem controlled_add_constant_t_cost (k : ℕ) :
    SatisfiesControlledAddConstantTBound k (controlledAddConstantTCost k) :=
  controlled_add_constant_baseline_t_bound k

/-- Claimed spacetime cost of `controlledAddConstantProgram`, as a function of the bit-width `k`. -/
def controlledAddConstantSpacetimeCost (k : ℕ) : ℕ := 4 * (k - 1) * (1 + k + 2 * k)

theorem controlled_add_constant_spacetime_cost (k : ℕ) :
    SatisfiesControlledAddConstantSpacetimeBound k (controlledAddConstantSpacetimeCost k) :=
  controlled_add_constant_baseline_spacetime_bound k

/-!
## Cost Theorems at the Pinned Bit-Widths `k = 64` and `k = 2048`
-/

/-- Claimed `T` count bound for `controlledAddConstantProgram` at `k = 64`. -/
def controlledAddConstantK64TCost : ℕ := 252

theorem controlled_add_constant_k64_t_cost :
    SatisfiesControlledAddConstantTBound 64 controlledAddConstantK64TCost :=
  controlled_add_constant_baseline_t_bound 64

/-- Claimed spacetime cost bound for `controlledAddConstantProgram` at `k = 64`. -/
def controlledAddConstantK64SpacetimeCost : ℕ := 48636

theorem controlled_add_constant_k64_spacetime_cost :
    SatisfiesControlledAddConstantSpacetimeBound 64 controlledAddConstantK64SpacetimeCost :=
  controlled_add_constant_baseline_spacetime_bound 64

/-- Claimed `T` count bound for `controlledAddConstantProgram` at `k = 2048`. -/
def controlledAddConstantK2048TCost : ℕ := 8188

theorem controlled_add_constant_k2048_t_cost :
    SatisfiesControlledAddConstantTBound 2048 controlledAddConstantK2048TCost :=
  controlled_add_constant_baseline_t_bound 2048

/-- Claimed spacetime cost bound for `controlledAddConstantProgram` at `k = 2048`. -/
def controlledAddConstantK2048SpacetimeCost : ℕ := 50315260

theorem controlled_add_constant_k2048_spacetime_cost :
    SatisfiesControlledAddConstantSpacetimeBound 2048 controlledAddConstantK2048SpacetimeCost :=
  controlled_add_constant_baseline_spacetime_bound 2048

end QuantumComputation.Specs
