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
# Addition of a Classical Constant (`addConstant`) Specification: Baseline Solution

Baseline: write the constant `a` into `k` clean ancilla wires with `X` gates, add those wires into
the data with the ripple-carry adder `ArcsinImpl.rippleSteps` (temporary-AND carries, measurement
based uncomputation), then erase the constant with the same `X` gates. It uses `2 * k` clean
ancillas (`k` constant wires, one zero carry-in wire and `k - 1` carry wires) and at most
`4 * (k - 1)` `T` gates. The specification text below is unchanged; only the holes are filled and
the theorems proved.

Parameterized specification for reversible in-place addition of a classical constant to a `k`-bit
quantum register, `|y⟩|0⟩^⊗m ↦ |(y + a) mod 2^k⟩|0⟩^⊗m`, for every bit-width `k` and every constant
`a` in `[0, 2^k)`. The register holds an unsigned integer, least-significant bit first, and the `m`
clean ancilla qubits are returned to zero. The constant is known when the circuit is built, so the
program may depend on `a`; the ancilla count and both claimed costs depend only on `k` and must hold
for the worst constant.

There are two resource metrics over Clifford + `T` with measurements: the `T` count, and spacetime
(`T count * qubits`), where `qubits = k + addConstantAncillas k` is the total number of data and
clean ancilla qubits. Each metric has three cost theorems. One bounds the cost at every bit-width
`k` and every constant `a` by a claimed function of `k`. The other two pin the bit-widths `k = 64`
and `k = 2048` and bound the cost by a claimed closed constant, so that two solutions can be
compared by a number. `TOFF` gates are excluded, so each Toffoli is costed by its Clifford + `T`
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
## Reversible Constant-Addition Unitary
-/

/-- Ideal `k`-qubit unitary `|y⟩ ↦ |(y + a) mod 2^k⟩` for a classical constant `a : Fin (2 ^ k)`. -/
noncomputable abbrev addConstantUnitary (k : ℕ) (a : Fin (2 ^ k)) : Unitary (2 ^ k) :=
  permutationUnitary (Equiv.addRight a)

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive AddConstant.Var where | v deriving DecidableEq, Inhabited

open AddConstant (Var)
open AddConstant.Var (v)

/-!
## Baseline Construction
-/

namespace AddConstantImpl

open ArcsinImpl ArcsinImpl.Step

variable {n : ℕ}

/-- `X` the constant `a` into the clean wires `rAnc[0, k)`, ripple-add them into `rData` with carry-in
wire `rAnc k` and carry wires `rAnc[k + 1, 2 k)`, then erase the constant again. -/
def addConstantSteps :
    (k : ℕ) → Fin (2 ^ k) → QRegister k n → QRegister (2 * k) n → List (Step n)
  | 0, _, _, _ => []
  | K + 1, a, rData, rAnc =>
      xorSteps none (K + 1) (rAnc.slice 0 (K + 1) (by omega)) (basisBits (K + 1) a) ++
        rippleSteps K (rAnc.slice 0 (K + 1) (by omega)) rData (rAnc ⟨K + 1, by omega⟩)
          (rAnc.slice (K + 2) K (by omega)) ++
        xorSteps none (K + 1) (rAnc.slice 0 (K + 1) (by omega)) (basisBits (K + 1) a)

theorem andCount_addConstantSteps (k : ℕ) (a : Fin (2 ^ k)) (rData : QRegister k n)
    (rAnc : QRegister (2 * k) n) :
    ((addConstantSteps k a rData rAnc).map Step.andCount).sum = k - 1 := by
  cases k with
  | zero => rfl
  | succ K =>
    rw [addConstantSteps, List.map_append, List.map_append, List.sum_append, List.sum_append,
      andCount_xorSteps, andCount_rippleSteps]
    omega

/-- Writing `d` into the clean wires `rY` and writing it again cancels. -/
theorem writeReg_cancel {k : ℕ} (β : BitAssignment n) (rY rB : QRegister k n)
    (hYB : rY.DisjointWires rB) (d g : BitAssignment k) (hY : ∀ i, β (rY i) = 0) :
    writeReg (writeReg (writeReg β rY d) rB g) rY
        (fun i ↦ writeReg (writeReg β rY d) rB g (rY i) +
          ctrlVal none (writeReg (writeReg β rY d) rB g) * d i) =
      writeReg β rB g := by
  have h2 : ∀ x : ZMod 2, x + 1 * x = 0 := by decide
  funext w
  by_cases hw1 : w ∈ Set.range rY.wires
  · obtain ⟨i, rfl⟩ := hw1
    have hi : rY i ∉ Set.range rB.wires := not_mem_of_disjoint hYB i
    simp only [writeReg_apply_reg, writeReg_apply_of_not_mem _ _ _ _ hi, hY i, ctrlVal, h2]
  · by_cases hw2 : w ∈ Set.range rB.wires
    · obtain ⟨i, rfl⟩ := hw2
      have hi : rB i ∉ Set.range rY.wires := not_mem_of_disjoint (QRegister.disjoint_comm.mp hYB) i
      simp only [writeReg_apply_of_not_mem _ _ _ _ hi, writeReg_apply_reg]
    · simp only [writeReg_apply_of_not_mem _ _ _ _ hw1, writeReg_apply_of_not_mem _ _ _ _ hw2]

theorem runList_addConstantCore (K : ℕ) (d : BitAssignment (K + 1)) (rY rB : QRegister (K + 1) n)
    (ci : Wire n) (rC : QRegister K n) (hYB : rY.DisjointWires rB) (hYC : rY.DisjointWires rC)
    (hBC : rB.DisjointWires rC) (hA : ci ∉ Set.range rY.wires) (hB : ci ∉ Set.range rB.wires)
    (hC : ci ∉ Set.range rC.wires) (β : BitAssignment n) (hY : ∀ i, β (rY i) = 0)
    (hci : β ci = 0) (hC0 : ∀ i, β (rC i) = 0) :
    runList (xorSteps none (K + 1) rY d ++ rippleSteps K rY rB ci rC ++
        xorSteps none (K + 1) rY d) β =
      some (writeReg β rB (basisBits (K + 1)
        ⟨((((basisBits (K + 1)).symm d : Fin (2 ^ (K + 1))) : ℕ) + (localIdx rB β : ℕ)) %
            2 ^ (K + 1), Nat.mod_lt _ (by positivity)⟩)) := by
  have hd : (fun i ↦ β (rY i) + ctrlVal none β * d i) = d :=
    funext fun i ↦ by simp [ctrlVal, hY i]
  have h1 : runList (xorSteps none (K + 1) rY d) β = some (writeReg β rY d) := by
    rw [runList_xorSteps none _ _ _ (fun i ↦ ctrlNe_none _), hd]
  have hC1 : ∀ i, writeReg β rY d (rC i) = 0 := fun i ↦ by
    rw [writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hYC) i)]
    exact hC0 i
  have hidx : (⟨((localIdx rY (writeReg β rY d) : ℕ) + (localIdx rB (writeReg β rY d) : ℕ) +
        (writeReg β rY d ci).val) % 2 ^ (K + 1), Nat.mod_lt _ (by positivity)⟩ :
        Fin (2 ^ (K + 1))) =
      ⟨((((basisBits (K + 1)).symm d : Fin (2 ^ (K + 1))) : ℕ) + (localIdx rB β : ℕ)) %
        2 ^ (K + 1), Nat.mod_lt _ (by positivity)⟩ := by
    apply Fin.ext
    simp only [localIdx_writeReg, localIdx_writeReg_of_disjoint β rY rB hYB d,
      writeReg_apply_of_not_mem β rY d ci hA, hci, ZMod.val_zero, add_zero]
  rw [runList_append, runList_append, h1, Option.bind_some,
    runList_rippleSteps K rY rB ci rC hYB hYC hBC hA hB hC _ hC1, Option.bind_some,
    runList_xorSteps none _ _ _ (fun i ↦ ctrlNe_none _), hidx]
  exact congrArg some (writeReg_cancel β rY rB hYB d _ hY)

theorem runList_addConstantSteps (k : ℕ) (a : Fin (2 ^ k)) (rData : QRegister k n)
    (rAnc : QRegister (2 * k) n) (hdisj : rData.DisjointWires rAnc) (β : BitAssignment n)
    (hβ : localIdx rAnc β = 0) :
    runList (addConstantSteps k a rData rAnc) β =
      some (writeReg β rData (basisBits k (Equiv.addRight a (localIdx rData β)))) := by
  cases k with
  | zero =>
    have h : Equiv.addRight a (localIdx rData β) = localIdx rData β := Fin.ext (by
      have h1 := (Equiv.addRight a (localIdx rData β)).isLt
      have h2 := (localIdx rData β).isLt
      simp only [pow_zero] at h1 h2
      omega)
    rw [addConstantSteps, runList_nil, h, basisBits_basisBitsEquiv_symm, writeReg_self]
  | succ K =>
    have hclean := eq_zero_of_localIdx_eq_zero rAnc β hβ
    have hRA : ∀ {b : ℕ} (r' : QRegister b (2 * (K + 1))),
        rData.DisjointWires (rAnc.compose r') := fun _ ↦ hdisj.compose_right _
    rw [addConstantSteps, runList_addConstantCore K (basisBits (K + 1) a) _ rData _ _
      (QRegister.disjoint_comm.mp (hRA _))
      (QRegister.slice_disjoint_of_le rAnc 0 (K + 1) (K + 2) K (by omega) (by omega) (by omega))
      (hRA _) (apply_not_mem_slice rAnc ⟨K + 1, by omega⟩ 0 (K + 1) (by omega)
        (Or.inr (by simp)))
      (fun ⟨_, h⟩ ↦ hdisj.ne _ _ h)
      (apply_not_mem_slice rAnc ⟨K + 1, by omega⟩ (K + 2) K (by omega)
        (Or.inl (by dsimp; omega)))
      β (fun _ ↦ hclean _) (hclean _) (fun _ ↦ hclean _)]
    refine congrArg some (congrArg _ (congrArg _ (Fin.ext ?_)))
    simp only [basisBitsEquiv_symm_basisBits, Equiv.coe_addRight, Fin.val_add, Nat.add_comm]

end AddConstantImpl

open ArcsinImpl ArcsinImpl.Step

/-- Number of clean ancilla qubits `addConstantProgram` uses at bit-width `k`. -/
def addConstantAncillas (k : ℕ) : ℕ := 2 * k

/-- Parameterized constant adder on `k` data wires `rData` (least-significant bit first) and
`addConstantAncillas k` clean ancilla wires `rAnc`. -/
def addConstantProgram {n : ℕ} (k : ℕ) (a : Fin (2 ^ k))
    (rData : QRegister k n)
    (rAnc : QRegister (addConstantAncillas k) n) : DynamicCircuit Var n :=
  compileList v (AddConstantImpl.addConstantSteps k a rData rAnc)

/-- Parameterized correctness theorem: for every bit-width `k` and every constant `a : Fin (2 ^ k)`,
`addConstantProgram k a` realizes `addConstantUnitary k a` as an exact clean subroutine across all
disjoint register placements. -/
theorem add_constant_correctness (k : ℕ) (a : Fin (2 ^ k)) :
    ∀ {n : ℕ}
      (rData : QRegister k n)
      (rAnc : QRegister (addConstantAncillas k) n)
      (hdisj : rData.DisjointWires rAnc),
      RealizesCleanSubroutine rData rAnc hdisj (addConstantUnitary k a)
        (addConstantProgram k a rData rAnc).compile := by
  intro n rData rAnc hdisj
  exact realizesCleanSubroutine_compileList v _ rData rAnc hdisj (Equiv.addRight a) fun β hβ ↦
    AddConstantImpl.runList_addConstantSteps k a rData rAnc hdisj β hβ

/-- `T`-gate count of `addConstantProgram k a`, which the cost predicates require to use no `TOFF`
gates. -/
abbrev addConstantTCount {n : ℕ} (k : ℕ) (a : Fin (2 ^ k))
    (rData : QRegister k n)
    (rAnc : QRegister (addConstantAncillas k) n) : ℕ :=
  (addConstantProgram k a rData rAnc).count PrimitiveGate.T

/-- Spacetime cost `T count * qubits` of `addConstantProgram k a`, counting all
`k + addConstantAncillas k` data and clean ancilla qubits. -/
abbrev addConstantSpacetime {n : ℕ} (k : ℕ) (a : Fin (2 ^ k))
    (rData : QRegister k n)
    (rAnc : QRegister (addConstantAncillas k) n) : ℕ :=
  addConstantTCount k a rData rAnc * (k + addConstantAncillas k)

/-!
## Cost Predicates

Both predicates forbid primitive `TOFF` gates (so every Toffoli must be decomposed into Clifford +
`T` + measurements) and bound a cost of `addConstantProgram` at bit-width `k` and every constant
`a : Fin (2 ^ k)` across all register placements.
-/

/-- `addConstantProgram` at bit-width `k` uses no primitive `TOFF` gates and has `T` count at most
`cost`, for every constant and register placement it can be given. -/
abbrev SatisfiesAddConstantTBound (k cost : ℕ) : Prop :=
  ∀ (a : Fin (2 ^ k)) {n : ℕ}
    (rData : QRegister k n)
    (rAnc : QRegister (addConstantAncillas k) n),
    (addConstantProgram k a rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      addConstantTCount k a rData rAnc ≤ cost

/-- `addConstantProgram` at bit-width `k` uses no primitive `TOFF` gates and has spacetime cost at
most `cost`, for every constant and register placement it can be given. -/
abbrev SatisfiesAddConstantSpacetimeBound (k cost : ℕ) : Prop :=
  ∀ (a : Fin (2 ^ k)) {n : ℕ}
    (rData : QRegister k n)
    (rAnc : QRegister (addConstantAncillas k) n),
    (addConstantProgram k a rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      addConstantSpacetime k a rData rAnc ≤ cost

/-- The baseline uses no `TOFF` gates and at most `4 * (k - 1)` `T` gates. -/
theorem add_constant_baseline_t_bound (k : ℕ) :
    SatisfiesAddConstantTBound k (4 * (k - 1)) := by
  intro a n rData rAnc
  refine ⟨count_TOFF_compileList v _, ?_⟩
  have h := count_T_compileList v (AddConstantImpl.addConstantSteps k a rData rAnc)
  exact h.trans (le_of_eq (congrArg (4 * ·)
    (AddConstantImpl.andCount_addConstantSteps k a rData rAnc)))

/-- The baseline has spacetime cost at most `4 * (k - 1) * (k + 2 * k)`. -/
theorem add_constant_baseline_spacetime_bound (k : ℕ) :
    SatisfiesAddConstantSpacetimeBound k (4 * (k - 1) * (k + 2 * k)) := by
  intro a n rData rAnc
  exact ⟨(add_constant_baseline_t_bound k a rData rAnc).1,
    Nat.mul_le_mul_right _ (add_constant_baseline_t_bound k a rData rAnc).2⟩

/-!
## Cost Theorems at Every Bit-Width
-/

/-- Claimed `T` count of `addConstantProgram`, as a function of the bit-width `k`. -/
def addConstantTCost (k : ℕ) : ℕ := 4 * (k - 1)

theorem add_constant_t_cost (k : ℕ) :
    SatisfiesAddConstantTBound k (addConstantTCost k) :=
  add_constant_baseline_t_bound k

/-- Claimed spacetime cost of `addConstantProgram`, as a function of the bit-width `k`. -/
def addConstantSpacetimeCost (k : ℕ) : ℕ := 4 * (k - 1) * (k + 2 * k)

theorem add_constant_spacetime_cost (k : ℕ) :
    SatisfiesAddConstantSpacetimeBound k (addConstantSpacetimeCost k) :=
  add_constant_baseline_spacetime_bound k

/-!
## Cost Theorems at the Pinned Bit-Widths `k = 64` and `k = 2048`
-/

/-- Claimed `T` count bound for `addConstantProgram` at `k = 64`. -/
def addConstantK64TCost : ℕ := 252

theorem add_constant_k64_t_cost :
    SatisfiesAddConstantTBound 64 addConstantK64TCost :=
  add_constant_baseline_t_bound 64

/-- Claimed spacetime cost bound for `addConstantProgram` at `k = 64`. -/
def addConstantK64SpacetimeCost : ℕ := 48384

theorem add_constant_k64_spacetime_cost :
    SatisfiesAddConstantSpacetimeBound 64 addConstantK64SpacetimeCost :=
  add_constant_baseline_spacetime_bound 64

/-- Claimed `T` count bound for `addConstantProgram` at `k = 2048`. -/
def addConstantK2048TCost : ℕ := 8188

theorem add_constant_k2048_t_cost :
    SatisfiesAddConstantTBound 2048 addConstantK2048TCost :=
  add_constant_baseline_t_bound 2048

/-- Claimed spacetime cost bound for `addConstantProgram` at `k = 2048`. -/
def addConstantK2048SpacetimeCost : ℕ := 50307072

theorem add_constant_k2048_spacetime_cost :
    SatisfiesAddConstantSpacetimeBound 2048 addConstantK2048SpacetimeCost :=
  add_constant_baseline_spacetime_bound 2048

end QuantumComputation.Specs
