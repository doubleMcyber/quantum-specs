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
# Less-Than Comparison with a Classical Constant (`compareConstant`) Specification

Parameterized specification for reversible comparison of a `k`-bit quantum register with a classical
constant, `|x⟩|t⟩|0⟩^⊗m ↦ |x⟩|t ⊕ [x < a]⟩|0⟩^⊗m`, for every bit-width `k` and every constant `a` in
`[0, 2^k)`. The register holds an unsigned integer in `[0, 2^k)`, least-significant bit first, and
is preserved. The flag qubit `t` is flipped exactly when `x < a` (strict), and the `m` clean ancilla
qubits are returned to zero. The relation `x ≥ a` follows by applying an `X` gate to the flag, at no
`T` cost. The constant is known when the circuit is built, so the program may depend on `a`; the
ancilla count and both claimed costs depend only on `k` and must hold for the worst constant. Kets
are written with the most significant register on the left, so the rightmost register occupies the
lowest wires.

There are two resource metrics over Clifford + `T` with measurements: the `T` count, and spacetime
(`T count * qubits`), where `qubits = k + 1 + compareConstantAncillas k` is the total number of data
and clean ancilla qubits. Each metric has three cost theorems. One bounds the cost at every
bit-width `k` and every constant `a` by a claimed function of `k`. The other two pin the bit-widths
`k = 64` and `k = 2048` and bound the cost by a claimed closed constant, so that two solutions can
be compared by a number. `TOFF` gates are excluded, so each Toffoli is costed by its Clifford + `T`
construction, such as `4` `T` gates with an ancilla and a measurement (C. Jones, Phys. Rev. A 87,
022328 (2013)).

References for the textbook constructions:
* S. A. Cuccaro, T. G. Draper, S. A. Kutin, D. P. Moulton, "A new quantum ripple-carry addition
  circuit", arXiv:quant-ph/0410184.
* C. Gidney, "Halving the cost of quantum addition", Quantum 2, 74 (2018), arXiv:1709.06648.
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator

/-!
## Reversible Constant-Comparison Unitary
-/

/-- The comparison flag `[x < a]` as a one-bit table on the `k`-qubit basis index `x`. -/
def lessThanConstantFlag {k : ℕ} (a : Fin (2 ^ k)) (x : Fin (2 ^ k)) : Fin (2 ^ 1) :=
  if x < a then 1 else 0

/-- Ideal `(k + 1)`-qubit unitary `|x⟩|t⟩ ↦ |x⟩|t ⊕ [x < a]⟩`: the basis permutation `tableAddPerm`
of `lessThanConstantFlag a`, with the flag `t` as the lowest bit of the basis index. -/
noncomputable abbrev compareConstantUnitary (k : ℕ) (a : Fin (2 ^ k)) : Unitary (2 ^ (k + 1)) :=
  permutationUnitary (tableAddPerm (lessThanConstantFlag a))

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive CompareConstant.Var where | v deriving DecidableEq, Inhabited

open CompareConstant (Var)
open CompareConstant.Var (v)

/-- Number of clean ancilla qubits `compareConstantProgram` uses at bit-width `k`. -/
def compareConstantAncillas (k : ℕ) : ℕ := sorry

/-- Parameterized constant comparator on `k + 1` data wires `rData` (the flag wire `t`, followed by
`k` wires `x`, least-significant bit first) and `compareConstantAncillas k` clean ancilla wires
`rAnc`. -/
def compareConstantProgram {n : ℕ} (k : ℕ) (a : Fin (2 ^ k))
    (rData : QRegister (k + 1) n)
    (rAnc : QRegister (compareConstantAncillas k) n) : DynamicCircuit Var n :=
  sorry

/-- Parameterized correctness theorem: for every bit-width `k` and every constant `a : Fin (2 ^ k)`,
`compareConstantProgram k a` realizes `compareConstantUnitary k a` as an exact clean subroutine
across all disjoint register placements. -/
theorem compare_constant_correctness (k : ℕ) (a : Fin (2 ^ k)) :
    ∀ {n : ℕ}
      (rData : QRegister (k + 1) n)
      (rAnc : QRegister (compareConstantAncillas k) n)
      (hdisj : rData.DisjointWires rAnc),
      RealizesCleanSubroutine rData rAnc hdisj (compareConstantUnitary k a)
        (compareConstantProgram k a rData rAnc).compile := by sorry

/-- `T`-gate count of `compareConstantProgram k a`, which the cost predicates require to use no
`TOFF` gates. -/
abbrev compareConstantTCount {n : ℕ} (k : ℕ) (a : Fin (2 ^ k))
    (rData : QRegister (k + 1) n)
    (rAnc : QRegister (compareConstantAncillas k) n) : ℕ :=
  (compareConstantProgram k a rData rAnc).count PrimitiveGate.T

/-- Spacetime cost `T count * qubits` of `compareConstantProgram k a`, counting all
`k + 1 + compareConstantAncillas k` data and clean ancilla qubits. -/
abbrev compareConstantSpacetime {n : ℕ} (k : ℕ) (a : Fin (2 ^ k))
    (rData : QRegister (k + 1) n)
    (rAnc : QRegister (compareConstantAncillas k) n) : ℕ :=
  compareConstantTCount k a rData rAnc * (k + 1 + compareConstantAncillas k)

/-!
## Cost Predicates

Both predicates forbid primitive `TOFF` gates (so every Toffoli must be decomposed into Clifford +
`T` + measurements) and bound a cost of `compareConstantProgram` at bit-width `k` and every constant
`a : Fin (2 ^ k)` across all register placements.
-/

/-- `compareConstantProgram` at bit-width `k` uses no primitive `TOFF` gates and has `T` count at
most `cost`, for every constant and register placement it can be given. -/
abbrev SatisfiesCompareConstantTBound (k cost : ℕ) : Prop :=
  ∀ (a : Fin (2 ^ k)) {n : ℕ}
    (rData : QRegister (k + 1) n)
    (rAnc : QRegister (compareConstantAncillas k) n),
    (compareConstantProgram k a rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      compareConstantTCount k a rData rAnc ≤ cost

/-- `compareConstantProgram` at bit-width `k` uses no primitive `TOFF` gates and has spacetime cost
at most `cost`, for every constant and register placement it can be given. -/
abbrev SatisfiesCompareConstantSpacetimeBound (k cost : ℕ) : Prop :=
  ∀ (a : Fin (2 ^ k)) {n : ℕ}
    (rData : QRegister (k + 1) n)
    (rAnc : QRegister (compareConstantAncillas k) n),
    (compareConstantProgram k a rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      compareConstantSpacetime k a rData rAnc ≤ cost

/-!
## Cost Theorems at Every Bit-Width
-/

/-- Claimed `T` count of `compareConstantProgram`, as a function of the bit-width `k`. -/
def compareConstantTCost (k : ℕ) : ℕ := sorry

theorem compare_constant_t_cost (k : ℕ) :
    SatisfiesCompareConstantTBound k (compareConstantTCost k) := by sorry

/-- Claimed spacetime cost of `compareConstantProgram`, as a function of the bit-width `k`. -/
def compareConstantSpacetimeCost (k : ℕ) : ℕ := sorry

theorem compare_constant_spacetime_cost (k : ℕ) :
    SatisfiesCompareConstantSpacetimeBound k (compareConstantSpacetimeCost k) := by sorry

/-!
## Cost Theorems at the Pinned Bit-Widths `k = 64` and `k = 2048`
-/

/-- Claimed `T` count bound for `compareConstantProgram` at `k = 64`. -/
def compareConstantK64TCost : ℕ := sorry

theorem compare_constant_k64_t_cost :
    SatisfiesCompareConstantTBound 64 compareConstantK64TCost := by sorry

/-- Claimed spacetime cost bound for `compareConstantProgram` at `k = 64`. -/
def compareConstantK64SpacetimeCost : ℕ := sorry

theorem compare_constant_k64_spacetime_cost :
    SatisfiesCompareConstantSpacetimeBound 64 compareConstantK64SpacetimeCost := by sorry

/-- Claimed `T` count bound for `compareConstantProgram` at `k = 2048`. -/
def compareConstantK2048TCost : ℕ := sorry

theorem compare_constant_k2048_t_cost :
    SatisfiesCompareConstantTBound 2048 compareConstantK2048TCost := by sorry

/-- Claimed spacetime cost bound for `compareConstantProgram` at `k = 2048`. -/
def compareConstantK2048SpacetimeCost : ℕ := sorry

theorem compare_constant_k2048_spacetime_cost :
    SatisfiesCompareConstantSpacetimeBound 2048 compareConstantK2048SpacetimeCost := by sorry

end QuantumComputation.Specs
