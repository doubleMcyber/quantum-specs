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
# Addition of a Classical Constant (`addConstant`) Specification

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

/-- Number of clean ancilla qubits `addConstantProgram` uses at bit-width `k`. -/
def addConstantAncillas (k : ℕ) : ℕ := sorry

/-- Parameterized constant adder on `k` data wires `rData` (least-significant bit first) and
`addConstantAncillas k` clean ancilla wires `rAnc`. -/
def addConstantProgram {n : ℕ} (k : ℕ) (a : Fin (2 ^ k))
    (rData : QRegister k n)
    (rAnc : QRegister (addConstantAncillas k) n) : DynamicCircuit Var n :=
  sorry

/-- Parameterized correctness theorem: for every bit-width `k` and every constant `a : Fin (2 ^ k)`,
`addConstantProgram k a` realizes `addConstantUnitary k a` as an exact clean subroutine across all
disjoint register placements. -/
theorem add_constant_correctness (k : ℕ) (a : Fin (2 ^ k)) :
    ∀ {n : ℕ}
      (rData : QRegister k n)
      (rAnc : QRegister (addConstantAncillas k) n)
      (hdisj : rData.DisjointWires rAnc),
      RealizesCleanSubroutine rData rAnc hdisj (addConstantUnitary k a)
        (addConstantProgram k a rData rAnc).compile := by sorry

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

/-!
## Cost Theorems at Every Bit-Width
-/

/-- Claimed `T` count of `addConstantProgram`, as a function of the bit-width `k`. -/
def addConstantTCost (k : ℕ) : ℕ := sorry

theorem add_constant_t_cost (k : ℕ) :
    SatisfiesAddConstantTBound k (addConstantTCost k) := by sorry

/-- Claimed spacetime cost of `addConstantProgram`, as a function of the bit-width `k`. -/
def addConstantSpacetimeCost (k : ℕ) : ℕ := sorry

theorem add_constant_spacetime_cost (k : ℕ) :
    SatisfiesAddConstantSpacetimeBound k (addConstantSpacetimeCost k) := by sorry

/-!
## Cost Theorems at the Pinned Bit-Widths `k = 64` and `k = 2048`
-/

/-- Claimed `T` count bound for `addConstantProgram` at `k = 64`. -/
def addConstantK64TCost : ℕ := sorry

theorem add_constant_k64_t_cost :
    SatisfiesAddConstantTBound 64 addConstantK64TCost := by sorry

/-- Claimed spacetime cost bound for `addConstantProgram` at `k = 64`. -/
def addConstantK64SpacetimeCost : ℕ := sorry

theorem add_constant_k64_spacetime_cost :
    SatisfiesAddConstantSpacetimeBound 64 addConstantK64SpacetimeCost := by sorry

/-- Claimed `T` count bound for `addConstantProgram` at `k = 2048`. -/
def addConstantK2048TCost : ℕ := sorry

theorem add_constant_k2048_t_cost :
    SatisfiesAddConstantTBound 2048 addConstantK2048TCost := by sorry

/-- Claimed spacetime cost bound for `addConstantProgram` at `k = 2048`. -/
def addConstantK2048SpacetimeCost : ℕ := sorry

theorem add_constant_k2048_spacetime_cost :
    SatisfiesAddConstantSpacetimeBound 2048 addConstantK2048SpacetimeCost := by sorry

end QuantumComputation.Specs
