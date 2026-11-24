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
# In-Place Addition (`adder`) Specification

Parameterized specification for reversible in-place addition of two `k`-bit quantum registers,
`|x⟩|b⟩|0⟩^⊗m ↦ |x⟩|(b + x) mod 2^k⟩|0⟩^⊗m`, for every bit-width `k`. Both registers hold unsigned
integers in `[0, 2^k)`, least-significant bit first. The addend `x` is preserved, the target `b` is
overwritten by the sum modulo `2^k` (no carry-out qubit), and the `m` clean ancilla qubits are
returned to zero. Kets are written with the most significant register on the left, so the rightmost
register occupies the lowest wires. Since addition modulo `2^k` is the same map for unsigned and for
two's-complement integers, the specification covers both.

There are two resource metrics over Clifford + `T` with measurements: the `T` count, and spacetime
(`T count * qubits`), where `qubits = 2 * k + adderAncillas k` is the total number of data and clean
ancilla qubits. Each metric has three cost theorems. One bounds the cost at every bit-width `k` by a
claimed function of `k`. The other two pin the bit-widths `k = 64` and `k = 2048` and bound the cost
by a claimed closed constant, so that two solutions can be compared by a number. `TOFF` gates are
excluded, so each Toffoli is costed by its Clifford + `T` construction, such as `4` `T` gates with
an ancilla and a measurement (C. Jones, Phys. Rev. A 87, 022328 (2013)).

References for the textbook constructions:
* S. A. Cuccaro, T. G. Draper, S. A. Kutin, D. P. Moulton, "A new quantum ripple-carry addition
  circuit", arXiv:quant-ph/0410184 (one ancilla, `2k - 1` Toffolis without carry-out).
* C. Gidney, "Halving the cost of quantum addition", Quantum 2, 74 (2018), arXiv:1709.06648
  (`k - 1` ancillas, `4k + O(1)` `T` gates with measurement-based uncomputation).
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator

/-!
## Reversible In-Place Addition Unitary
-/

/-- Ideal `2k`-qubit unitary `|x⟩|b⟩ ↦ |x⟩|(b + x) mod 2^k⟩`: the basis permutation
`equalTableAddPerm` of the identity table, which splits a basis index of `Fin (2 ^ (2 * k))` into
the addend `x` (high half) and the target `b` (low half). -/
noncomputable abbrev adderUnitary (k : ℕ) : Unitary (2 ^ (2 * k)) :=
  permutationUnitary (equalTableAddPerm (fun x : Fin (2 ^ k) ↦ x))

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive Adder.Var where | v deriving DecidableEq, Inhabited

open Adder (Var)
open Adder.Var (v)

/-- Number of clean ancilla qubits `adderProgram` uses at bit-width `k`. -/
def adderAncillas (k : ℕ) : ℕ := sorry

/-- Parameterized in-place adder on `2 * k` data wires `rData` (`k` target wires `b` followed by `k`
addend wires `x`, each least-significant bit first, matching `finProdFinEquiv`) and
`adderAncillas k` clean ancilla wires `rAnc`. -/
def adderProgram {n : ℕ} (k : ℕ)
    (rData : QRegister (2 * k) n)
    (rAnc : QRegister (adderAncillas k) n) : DynamicCircuit Var n :=
  sorry

/-- Parameterized correctness theorem: for every bit-width `k`, `adderProgram k` realizes
`adderUnitary k` as an exact clean subroutine across all disjoint register placements. -/
theorem adder_correctness (k : ℕ) :
    ∀ {n : ℕ}
      (rData : QRegister (2 * k) n)
      (rAnc : QRegister (adderAncillas k) n)
      (hdisj : rData.DisjointWires rAnc),
      RealizesCleanSubroutine rData rAnc hdisj (adderUnitary k)
        (adderProgram k rData rAnc).compile := by sorry

/-- `T`-gate count of `adderProgram k`, which the cost predicates require to use no `TOFF` gates. -/
abbrev adderTCount {n : ℕ} (k : ℕ)
    (rData : QRegister (2 * k) n)
    (rAnc : QRegister (adderAncillas k) n) : ℕ :=
  (adderProgram k rData rAnc).count PrimitiveGate.T

/-- Spacetime cost `T count * qubits` of `adderProgram k`, counting all `2 * k + adderAncillas k`
data and clean ancilla qubits. -/
abbrev adderSpacetime {n : ℕ} (k : ℕ)
    (rData : QRegister (2 * k) n)
    (rAnc : QRegister (adderAncillas k) n) : ℕ :=
  adderTCount k rData rAnc * (2 * k + adderAncillas k)

/-!
## Cost Predicates

Both predicates forbid primitive `TOFF` gates (so every Toffoli must be decomposed into Clifford +
`T` + measurements) and bound a cost of `adderProgram` at bit-width `k` across all register
placements.
-/

/-- `adderProgram` at bit-width `k` uses no primitive `TOFF` gates and has `T` count at most `cost`,
across all register placements. -/
abbrev SatisfiesAdderTBound (k cost : ℕ) : Prop :=
  ∀ {n : ℕ}
    (rData : QRegister (2 * k) n)
    (rAnc : QRegister (adderAncillas k) n),
    (adderProgram k rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      adderTCount k rData rAnc ≤ cost

/-- `adderProgram` at bit-width `k` uses no primitive `TOFF` gates and has spacetime cost at most
`cost`, for every constant and register placement it can be given. -/
abbrev SatisfiesAdderSpacetimeBound (k cost : ℕ) : Prop :=
  ∀ {n : ℕ}
    (rData : QRegister (2 * k) n)
    (rAnc : QRegister (adderAncillas k) n),
    (adderProgram k rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      adderSpacetime k rData rAnc ≤ cost

/-!
## Cost Theorems at Every Bit-Width
-/

/-- Claimed `T` count of `adderProgram`, as a function of the bit-width `k`. -/
def adderTCost (k : ℕ) : ℕ := sorry

theorem adder_t_cost (k : ℕ) :
    SatisfiesAdderTBound k (adderTCost k) := by sorry

/-- Claimed spacetime cost of `adderProgram`, as a function of the bit-width `k`. -/
def adderSpacetimeCost (k : ℕ) : ℕ := sorry

theorem adder_spacetime_cost (k : ℕ) :
    SatisfiesAdderSpacetimeBound k (adderSpacetimeCost k) := by sorry

/-!
## Cost Theorems at the Pinned Bit-Widths `k = 64` and `k = 2048`
-/

/-- Claimed `T` count bound for `adderProgram` at `k = 64`. -/
def adderK64TCost : ℕ := sorry

theorem adder_k64_t_cost :
    SatisfiesAdderTBound 64 adderK64TCost := by sorry

/-- Claimed spacetime cost bound for `adderProgram` at `k = 64`. -/
def adderK64SpacetimeCost : ℕ := sorry

theorem adder_k64_spacetime_cost :
    SatisfiesAdderSpacetimeBound 64 adderK64SpacetimeCost := by sorry

/-- Claimed `T` count bound for `adderProgram` at `k = 2048`. -/
def adderK2048TCost : ℕ := sorry

theorem adder_k2048_t_cost :
    SatisfiesAdderTBound 2048 adderK2048TCost := by sorry

/-- Claimed spacetime cost bound for `adderProgram` at `k = 2048`. -/
def adderK2048SpacetimeCost : ℕ := sorry

theorem adder_k2048_spacetime_cost :
    SatisfiesAdderSpacetimeBound 2048 adderK2048SpacetimeCost := by sorry

end QuantumComputation.Specs
