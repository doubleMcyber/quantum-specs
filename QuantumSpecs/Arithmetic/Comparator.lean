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
# Less-Than Comparison (`comparator`) Specification

Parameterized specification for reversible comparison of two `k`-bit quantum registers,
`|y⟩|x⟩|t⟩|0⟩^⊗m ↦ |y⟩|x⟩|t ⊕ [x < y]⟩|0⟩^⊗m`, for every bit-width `k`. Both registers hold unsigned
integers in `[0, 2^k)`, least-significant bit first, and are preserved. The flag qubit `t` is
flipped exactly when `x < y` (strict), and the `m` clean ancilla qubits are returned to zero. The
other three order relations follow by exchanging the registers or applying an `X` gate to the flag,
at no `T` cost. Kets are written with the most significant register on the left, so the rightmost
register occupies the lowest wires.

There are two resource metrics over Clifford + `T` with measurements: the `T` count, and spacetime
(`T count * qubits`), where `qubits = 2 * k + 1 + comparatorAncillas k` is the total number of data
and clean ancilla qubits. Each metric has three cost theorems. One bounds the cost at every
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
## Reversible Comparison Unitary
-/

/-- The comparison flag `[x < y]` as a one-bit table on a `2k`-qubit basis index, which
`splitEqualBasisEquiv` splits into `y` (high half) and `x` (low half). -/
def lessThanFlag (k : ℕ) (u : Fin (2 ^ (2 * k))) : Fin (2 ^ 1) :=
  if (splitEqualBasisEquiv k u).2 < (splitEqualBasisEquiv k u).1 then 1 else 0

/-- Ideal `(2k + 1)`-qubit unitary `|y⟩|x⟩|t⟩ ↦ |y⟩|x⟩|t ⊕ [x < y]⟩`: the basis permutation
`tableAddPerm` of `lessThanFlag`, with the flag `t` as the lowest bit of the basis index. -/
noncomputable abbrev comparatorUnitary (k : ℕ) : Unitary (2 ^ (2 * k + 1)) :=
  permutationUnitary (tableAddPerm (lessThanFlag k))

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive Comparator.Var where | v deriving DecidableEq, Inhabited

open Comparator (Var)
open Comparator.Var (v)

/-- Number of clean ancilla qubits `comparatorProgram` uses at bit-width `k`. -/
def comparatorAncillas (k : ℕ) : ℕ := sorry

/-- Parameterized comparator on `2 * k + 1` data wires `rData` (the flag wire `t`, followed by `k`
wires `x` and then `k` wires `y`, each least-significant bit first) and `comparatorAncillas k` clean
ancilla wires `rAnc`. -/
def comparatorProgram {n : ℕ} (k : ℕ)
    (rData : QRegister (2 * k + 1) n)
    (rAnc : QRegister (comparatorAncillas k) n) : DynamicCircuit Var n :=
  sorry

/-- Parameterized correctness theorem: for every bit-width `k`, `comparatorProgram k` realizes
`comparatorUnitary k` as an exact clean subroutine across all disjoint register placements. -/
theorem comparator_correctness (k : ℕ) :
    ∀ {n : ℕ}
      (rData : QRegister (2 * k + 1) n)
      (rAnc : QRegister (comparatorAncillas k) n)
      (hdisj : rData.DisjointWires rAnc),
      RealizesCleanSubroutine rData rAnc hdisj (comparatorUnitary k)
        (comparatorProgram k rData rAnc).compile := by sorry

/-- `T`-gate count of `comparatorProgram k`, which the cost predicates require to use no `TOFF`
gates. -/
abbrev comparatorTCount {n : ℕ} (k : ℕ)
    (rData : QRegister (2 * k + 1) n)
    (rAnc : QRegister (comparatorAncillas k) n) : ℕ :=
  (comparatorProgram k rData rAnc).count PrimitiveGate.T

/-- Spacetime cost `T count * qubits` of `comparatorProgram k`, counting all
`2 * k + 1 + comparatorAncillas k` data and clean ancilla qubits. -/
abbrev comparatorSpacetime {n : ℕ} (k : ℕ)
    (rData : QRegister (2 * k + 1) n)
    (rAnc : QRegister (comparatorAncillas k) n) : ℕ :=
  comparatorTCount k rData rAnc * (2 * k + 1 + comparatorAncillas k)

/-!
## Cost Predicates

Both predicates forbid primitive `TOFF` gates (so every Toffoli must be decomposed into Clifford +
`T` + measurements) and bound a cost of `comparatorProgram` at bit-width `k` across all register
placements.
-/

/-- `comparatorProgram` at bit-width `k` uses no primitive `TOFF` gates and has `T` count at most
`cost`, across all register placements. -/
abbrev SatisfiesComparatorTBound (k cost : ℕ) : Prop :=
  ∀ {n : ℕ}
    (rData : QRegister (2 * k + 1) n)
    (rAnc : QRegister (comparatorAncillas k) n),
    (comparatorProgram k rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      comparatorTCount k rData rAnc ≤ cost

/-- `comparatorProgram` at bit-width `k` uses no primitive `TOFF` gates and has spacetime cost at
most `cost`, for every constant and register placement it can be given. -/
abbrev SatisfiesComparatorSpacetimeBound (k cost : ℕ) : Prop :=
  ∀ {n : ℕ}
    (rData : QRegister (2 * k + 1) n)
    (rAnc : QRegister (comparatorAncillas k) n),
    (comparatorProgram k rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      comparatorSpacetime k rData rAnc ≤ cost

/-!
## Cost Theorems at Every Bit-Width
-/

/-- Claimed `T` count of `comparatorProgram`, as a function of the bit-width `k`. -/
def comparatorTCost (k : ℕ) : ℕ := sorry

theorem comparator_t_cost (k : ℕ) :
    SatisfiesComparatorTBound k (comparatorTCost k) := by sorry

/-- Claimed spacetime cost of `comparatorProgram`, as a function of the bit-width `k`. -/
def comparatorSpacetimeCost (k : ℕ) : ℕ := sorry

theorem comparator_spacetime_cost (k : ℕ) :
    SatisfiesComparatorSpacetimeBound k (comparatorSpacetimeCost k) := by sorry

/-!
## Cost Theorems at the Pinned Bit-Widths `k = 64` and `k = 2048`
-/

/-- Claimed `T` count bound for `comparatorProgram` at `k = 64`. -/
def comparatorK64TCost : ℕ := sorry

theorem comparator_k64_t_cost :
    SatisfiesComparatorTBound 64 comparatorK64TCost := by sorry

/-- Claimed spacetime cost bound for `comparatorProgram` at `k = 64`. -/
def comparatorK64SpacetimeCost : ℕ := sorry

theorem comparator_k64_spacetime_cost :
    SatisfiesComparatorSpacetimeBound 64 comparatorK64SpacetimeCost := by sorry

/-- Claimed `T` count bound for `comparatorProgram` at `k = 2048`. -/
def comparatorK2048TCost : ℕ := sorry

theorem comparator_k2048_t_cost :
    SatisfiesComparatorTBound 2048 comparatorK2048TCost := by sorry

/-- Claimed spacetime cost bound for `comparatorProgram` at `k = 2048`. -/
def comparatorK2048SpacetimeCost : ℕ := sorry

theorem comparator_k2048_spacetime_cost :
    SatisfiesComparatorSpacetimeBound 2048 comparatorK2048SpacetimeCost := by sorry

end QuantumComputation.Specs
