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

/-!
# Controlled In-Place Addition (`controlledAdder`) Specification

Parameterized specification for reversible in-place addition of two `k`-bit quantum registers
controlled on one qubit, `|c⟩|x⟩|b⟩|0⟩^⊗m ↦ |c⟩|x⟩|(b + c * x) mod 2^k⟩|0⟩^⊗m`, for every bit-width
`k`. Both registers hold unsigned integers in `[0, 2^k)`, least-significant bit first. The control
`c` and the addend `x` are preserved, the target `b` is overwritten by the sum modulo `2^k` when
`c = 1` and is unchanged when `c = 0`, and the `m` clean ancilla qubits are returned to zero. Kets
are written with the most significant register on the left, so the rightmost register occupies the
lowest wires.

There are two resource metrics over Clifford + `T` with measurements: the `T` count, and spacetime
(`T count * qubits`), where `qubits = 1 + k + k + controlledAdderAncillas k` is the total number of
data and clean ancilla qubits. Each metric has three cost theorems. One bounds the cost at every
bit-width `k` by a claimed function of `k`. The other two pin the bit-widths `k = 64` and `k = 2048`
and bound the cost by a claimed closed constant, so that two solutions can be compared by a number.
`TOFF` gates are excluded, so each Toffoli is costed by its Clifford + `T` construction, such as `4`
`T` gates with an ancilla and a measurement (C. Jones, Phys. Rev. A 87, 022328 (2013)).

References for the textbook constructions:
* S. A. Cuccaro, T. G. Draper, S. A. Kutin, D. P. Moulton, "A new quantum ripple-carry addition
  circuit", arXiv:quant-ph/0410184.
* C. Gidney, "Halving the cost of quantum addition", Quantum 2, 74 (2018), arXiv:1709.06648.
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator

/-!
## Reversible Controlled-Addition Unitary
-/

/-- The controlled addend `c * x` as a table on a `(1 + k)`-qubit basis index, which
`splitBasisEquiv` splits into the control `c` (highest bit) and the addend `x` (low `k` bits). -/
def controlledAddend (k : ℕ) (u : Fin (2 ^ (1 + k))) : Fin (2 ^ k) :=
  if (splitBasisEquiv 1 k u).1 = 1 then (splitBasisEquiv 1 k u).2 else 0

/-- Ideal `(1 + 2k)`-qubit unitary `|c⟩|x⟩|b⟩ ↦ |c⟩|x⟩|(b + c * x) mod 2^k⟩`: the basis permutation
`tableAddPerm` of `controlledAddend`, with the target `b` as the low `k` bits of the basis index. -/
noncomputable abbrev controlledAdderUnitary (k : ℕ) : Unitary (2 ^ (1 + k + k)) :=
  permutationUnitary (tableAddPerm (controlledAddend k))

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive ControlledAdder.Var where | v deriving DecidableEq, Inhabited

open ControlledAdder (Var)
open ControlledAdder.Var (v)

/-- Number of clean ancilla qubits `controlledAdderProgram` uses at bit-width `k`. -/
def controlledAdderAncillas (k : ℕ) : ℕ := sorry

/-- Parameterized controlled adder on `1 + k + k` data wires `rData` (`k` target wires `b`, followed
by `k` addend wires `x`, each least-significant bit first, and then the control wire `c`) and
`controlledAdderAncillas k` clean ancilla wires `rAnc`. -/
def controlledAdderProgram {n : ℕ} (k : ℕ)
    (rData : QRegister (1 + k + k) n)
    (rAnc : QRegister (controlledAdderAncillas k) n) : DynamicCircuit Var n :=
  sorry

/-- Parameterized correctness theorem: for every bit-width `k`, `controlledAdderProgram k` realizes
`controlledAdderUnitary k` as an exact clean subroutine across all disjoint register placements. -/
theorem controlled_adder_correctness (k : ℕ) :
    ∀ {n : ℕ}
      (rData : QRegister (1 + k + k) n)
      (rAnc : QRegister (controlledAdderAncillas k) n)
      (hdisj : rData.DisjointWires rAnc),
      RealizesCleanSubroutine rData rAnc hdisj (controlledAdderUnitary k)
        (controlledAdderProgram k rData rAnc).compile := by sorry

/-- `T`-gate count of `controlledAdderProgram k`, which the cost predicates require to use no `TOFF`
gates. -/
abbrev controlledAdderTCount {n : ℕ} (k : ℕ)
    (rData : QRegister (1 + k + k) n)
    (rAnc : QRegister (controlledAdderAncillas k) n) : ℕ :=
  (controlledAdderProgram k rData rAnc).count PrimitiveGate.T

/-- Spacetime cost `T count * qubits` of `controlledAdderProgram k`, counting all
`1 + k + k + controlledAdderAncillas k` data and clean ancilla qubits. -/
abbrev controlledAdderSpacetime {n : ℕ} (k : ℕ)
    (rData : QRegister (1 + k + k) n)
    (rAnc : QRegister (controlledAdderAncillas k) n) : ℕ :=
  controlledAdderTCount k rData rAnc * (1 + k + k + controlledAdderAncillas k)

/-!
## Cost Predicates

Both predicates forbid primitive `TOFF` gates (so every Toffoli must be decomposed into Clifford +
`T` + measurements) and bound a cost of `controlledAdderProgram` at bit-width `k` across all
register placements.
-/

/-- `controlledAdderProgram` at bit-width `k` uses no primitive `TOFF` gates and has `T` count at
most `cost`, across all register placements. -/
abbrev SatisfiesControlledAdderTBound (k cost : ℕ) : Prop :=
  ∀ {n : ℕ}
    (rData : QRegister (1 + k + k) n)
    (rAnc : QRegister (controlledAdderAncillas k) n),
    (controlledAdderProgram k rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      controlledAdderTCount k rData rAnc ≤ cost

/-- `controlledAdderProgram` at bit-width `k` uses no primitive `TOFF` gates and has spacetime cost
at most `cost`, for every constant and register placement it can be given. -/
abbrev SatisfiesControlledAdderSpacetimeBound (k cost : ℕ) : Prop :=
  ∀ {n : ℕ}
    (rData : QRegister (1 + k + k) n)
    (rAnc : QRegister (controlledAdderAncillas k) n),
    (controlledAdderProgram k rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      controlledAdderSpacetime k rData rAnc ≤ cost

/-!
## Cost Theorems at Every Bit-Width
-/

/-- Claimed `T` count of `controlledAdderProgram`, as a function of the bit-width `k`. -/
def controlledAdderTCost (k : ℕ) : ℕ := sorry

theorem controlled_adder_t_cost (k : ℕ) :
    SatisfiesControlledAdderTBound k (controlledAdderTCost k) := by sorry

/-- Claimed spacetime cost of `controlledAdderProgram`, as a function of the bit-width `k`. -/
def controlledAdderSpacetimeCost (k : ℕ) : ℕ := sorry

theorem controlled_adder_spacetime_cost (k : ℕ) :
    SatisfiesControlledAdderSpacetimeBound k (controlledAdderSpacetimeCost k) := by sorry

/-!
## Cost Theorems at the Pinned Bit-Widths `k = 64` and `k = 2048`
-/

/-- Claimed `T` count bound for `controlledAdderProgram` at `k = 64`. -/
def controlledAdderK64TCost : ℕ := sorry

theorem controlled_adder_k64_t_cost :
    SatisfiesControlledAdderTBound 64 controlledAdderK64TCost := by sorry

/-- Claimed spacetime cost bound for `controlledAdderProgram` at `k = 64`. -/
def controlledAdderK64SpacetimeCost : ℕ := sorry

theorem controlled_adder_k64_spacetime_cost :
    SatisfiesControlledAdderSpacetimeBound 64 controlledAdderK64SpacetimeCost := by sorry

/-- Claimed `T` count bound for `controlledAdderProgram` at `k = 2048`. -/
def controlledAdderK2048TCost : ℕ := sorry

theorem controlled_adder_k2048_t_cost :
    SatisfiesControlledAdderTBound 2048 controlledAdderK2048TCost := by sorry

/-- Claimed spacetime cost bound for `controlledAdderProgram` at `k = 2048`. -/
def controlledAdderK2048SpacetimeCost : ℕ := sorry

theorem controlled_adder_k2048_spacetime_cost :
    SatisfiesControlledAdderSpacetimeBound 2048 controlledAdderK2048SpacetimeCost := by sorry

end QuantumComputation.Specs
