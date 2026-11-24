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
# Controlled Addition of a Classical Constant (`controlledAddConstant`) Specification

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

/-- Number of clean ancilla qubits `controlledAddConstantProgram` uses at bit-width `k`. -/
def controlledAddConstantAncillas (k : ℕ) : ℕ := sorry

/-- Parameterized controlled constant adder on `1 + k` data wires `rData` (`k` target wires `y`,
least-significant bit first, followed by the control wire `c`) and `controlledAddConstantAncillas k`
clean ancilla wires `rAnc`. -/
def controlledAddConstantProgram {n : ℕ} (k : ℕ) (a : Fin (2 ^ k))
    (rData : QRegister (1 + k) n)
    (rAnc : QRegister (controlledAddConstantAncillas k) n) : DynamicCircuit Var n :=
  sorry

/-- Parameterized correctness theorem: for every bit-width `k` and every constant `a : Fin (2 ^ k)`,
`controlledAddConstantProgram k a` realizes `controlledAddConstantUnitary k a` as an exact clean
subroutine across all disjoint register placements. -/
theorem controlled_add_constant_correctness (k : ℕ) (a : Fin (2 ^ k)) :
    ∀ {n : ℕ}
      (rData : QRegister (1 + k) n)
      (rAnc : QRegister (controlledAddConstantAncillas k) n)
      (hdisj : rData.DisjointWires rAnc),
      RealizesCleanSubroutine rData rAnc hdisj (controlledAddConstantUnitary k a)
        (controlledAddConstantProgram k a rData rAnc).compile := by sorry

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

/-!
## Cost Theorems at Every Bit-Width
-/

/-- Claimed `T` count of `controlledAddConstantProgram`, as a function of the bit-width `k`. -/
def controlledAddConstantTCost (k : ℕ) : ℕ := sorry

theorem controlled_add_constant_t_cost (k : ℕ) :
    SatisfiesControlledAddConstantTBound k (controlledAddConstantTCost k) := by sorry

/-- Claimed spacetime cost of `controlledAddConstantProgram`, as a function of the bit-width `k`. -/
def controlledAddConstantSpacetimeCost (k : ℕ) : ℕ := sorry

theorem controlled_add_constant_spacetime_cost (k : ℕ) :
    SatisfiesControlledAddConstantSpacetimeBound k (controlledAddConstantSpacetimeCost k) := by
  sorry

/-!
## Cost Theorems at the Pinned Bit-Widths `k = 64` and `k = 2048`
-/

/-- Claimed `T` count bound for `controlledAddConstantProgram` at `k = 64`. -/
def controlledAddConstantK64TCost : ℕ := sorry

theorem controlled_add_constant_k64_t_cost :
    SatisfiesControlledAddConstantTBound 64 controlledAddConstantK64TCost := by sorry

/-- Claimed spacetime cost bound for `controlledAddConstantProgram` at `k = 64`. -/
def controlledAddConstantK64SpacetimeCost : ℕ := sorry

theorem controlled_add_constant_k64_spacetime_cost :
    SatisfiesControlledAddConstantSpacetimeBound 64 controlledAddConstantK64SpacetimeCost := by
  sorry

/-- Claimed `T` count bound for `controlledAddConstantProgram` at `k = 2048`. -/
def controlledAddConstantK2048TCost : ℕ := sorry

theorem controlled_add_constant_k2048_t_cost :
    SatisfiesControlledAddConstantTBound 2048 controlledAddConstantK2048TCost := by sorry

/-- Claimed spacetime cost bound for `controlledAddConstantProgram` at `k = 2048`. -/
def controlledAddConstantK2048SpacetimeCost : ℕ := sorry

theorem controlled_add_constant_k2048_spacetime_cost :
    SatisfiesControlledAddConstantSpacetimeBound 2048 controlledAddConstantK2048SpacetimeCost := by
  sorry

end QuantumComputation.Specs
