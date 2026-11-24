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
public import Mathlib.Algebra.Field.ZMod

/-!
# Prime-Field Multiplication (`fieldMul`) Specification

Parameterized specification for out-of-place multiplication of two quantum registers in a prime
field `𝔽_p`, `p` odd: `|x⟩|y⟩|t⟩|0⟩^⊗m ↦ |x⟩|y⟩|t + x * y mod p⟩|0⟩^⊗m` (giving
`|x⟩|y⟩|0⟩ ↦ |x⟩|y⟩|x * y mod p⟩` when `t = 0`).

Encoding: `w` is the bit length of `p` (`2^(w-1) < p < 2^w`). A triple `(x, y, t)` of field
elements is the computational-basis index `x + 2^w * y + 2^(2w) * t` of the `3 * w`-qubit data
register, with `x`, `y`, `t` the standard representatives in `[0, p)`: the first `w` wires hold
`x`, the next `w` hold `y` and the last `w` hold `t`, in the library's register convention (as in
`Arcsin`, matching `finProdFinEquiv`). Operands are plain residues, not Montgomery residues.

Valid inputs are the encodings of triples of field elements, that is, all three registers below
`p`. The action on other basis states is unconstrained, and inputs with nonzero ancillas are
unconstrained. The ancillas must be returned to zero.

The resource metric is the `T` count over Clifford + `T` with measurements, stated for every bit
length `w`, together with the spacetime (`T count * qubits`) at `w = 256`, where
`qubits = 3 * w + fieldMulAncillas w` is the total number of data and clean ancilla qubits. `TOFF`
gates are excluded, so each Toffoli is costed by its Clifford + `T` construction, such as `4` `T`
gates with an ancilla and a measurement (C. Jones, Phys. Rev. A 87, 022328 (2013)). Clifford
gates, measurements and classical control are not counted, and the program has one classical
variable for measurement outcomes.

Both cost theorems carry no hypotheses: the bound depends only on `w` and must hold for every
natural number `p` (prime or not, of any size) and every register placement, while correctness is
required only for odd primes of bit length `w`. So the bound is a worst case over all primes of
that bit length, with no credit for a special prime, and outside the correctness hypotheses the
program may be anything that meets the bound, such as the identity. The program may depend on `p`;
classical computation on it is not costed. The `T`-count theorem does not bound qubits: a
`T`-count claim is the pair (`fieldMulTCost w`, `3 * w + fieldMulAncillas w`), and only the
`w = 256` theorem combines the two into one number. The claimed costs are upper bounds supplied by
the solver; a smaller proved bound is a better solution.

References:
- M. Roetteler, M. Naehrig, K. M. Svore, K. Lauter, "Quantum resource estimates for computing
  elliptic curve discrete logarithms", ASIACRYPT 2017, arXiv:1706.06752.
- R. Rines, I. Chuang, "High performance quantum modular multipliers", arXiv:1801.01081.
- T. Häner, S. Jaques, M. Naehrig, M. Roetteler, M. Soeken, "Improved quantum circuits for elliptic
  curve discrete logarithms", PQCrypto 2020, arXiv:2001.09580.
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator

/-!
## Encoding & Valid Inputs
-/

/-- Basis index `(x + 2^w * y + 2^(2w) * t) mod 2^(3w)` of the `3 * w`-qubit data register
encoding the triple `(x, y, t)`, with `x`, `y`, `t` the standard representatives in `[0, p)`. The
reduction modulo `2^(3w)` only makes the definition total: it does nothing when `p ≤ 2^w`. -/
def fieldMulEncode (w : ℕ) {p : ℕ} (x y t : ZMod p) : Fin (2 ^ (3 * w)) :=
  ⟨(x.val + 2 ^ w * y.val + 2 ^ (2 * w) * t.val) % 2 ^ (3 * w), Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- Valid inputs: encodings of all triples of elements of `ZMod p`. -/
def fieldMulValidInputs (w p : ℕ) : Set (Fin (2 ^ (3 * w))) :=
  {u | ∃ x y t : ZMod p, u = fieldMulEncode w x y t}

/-- A basis permutation `σ` agrees with out-of-place multiplication in `ZMod p` on valid inputs:
it maps the encoding of `(x, y, t)` to the encoding of `(x, y, t + x * y)`. -/
def IsFieldMulPerm (w p : ℕ) (σ : Equiv.Perm (Fin (2 ^ (3 * w)))) : Prop :=
  ∀ x y t : ZMod p, σ (fieldMulEncode w x y t) = fieldMulEncode w x y (t + x * y)

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive FieldMul.Var where | v deriving DecidableEq, Inhabited

open FieldMul (Var)
open FieldMul.Var (v)

/-- Number of clean ancilla qubits `fieldMulProgram` uses at bit length `w`. -/
def fieldMulAncillas (w : ℕ) : ℕ := sorry

/-- Multiplication circuit modulo `p` on `3 * w` data wires `rData` (`w` wires for `x`, then `w`
for `y`, then `w` for the accumulator `t`) and `fieldMulAncillas w` clean ancilla wires `rAnc`. -/
def fieldMulProgram {n : ℕ} (w p : ℕ)
    (rData : QRegister (3 * w) n)
    (rAnc : QRegister (fieldMulAncillas w) n) : DynamicCircuit Var n :=
  sorry

/-- Parameterized correctness theorem: for an odd prime `p` of bit length `w`, there is a basis
permutation `σ` that maps `(x, y, t)` to `(x, y, t + x * y)` on all triples of field elements, and
`fieldMulProgram` realizes `σ` on valid inputs as a clean subroutine across all disjoint register
placements. -/
theorem fieldMul_correctness (w p : ℕ) [Fact p.Prime]
    (hp : 2 < p) (hlo : 2 ^ (w - 1) < p) (hhi : p < 2 ^ w) :
    ∃ σ : Equiv.Perm (Fin (2 ^ (3 * w))),
      IsFieldMulPerm w p σ ∧
      ∀ {n : ℕ}
        (rData : QRegister (3 * w) n)
        (rAnc : QRegister (fieldMulAncillas w) n)
        (hdisj : rData.DisjointWires rAnc),
        RealizesCleanSubroutineOnEncoding rData rAnc hdisj (fieldMulValidInputs w p) σ
          (fieldMulProgram w p rData rAnc).compile := by sorry

/-!
## `T`-Count Cost Target (all bit lengths)
-/

/-- Claimed `T` count of `fieldMulProgram` at bit length `w`. -/
def fieldMulTCost (w : ℕ) : ℕ := sorry

/-- For every modulus, `fieldMulProgram` uses no primitive `TOFF` gates and at most
`fieldMulTCost w` `T` gates, across all register placements. -/
theorem fieldMul_t_cost (w p : ℕ) {n : ℕ}
    (rData : QRegister (3 * w) n)
    (rAnc : QRegister (fieldMulAncillas w) n) :
    let P := fieldMulProgram w p rData rAnc
    P.count PrimitiveGate.TOFF = 0 ∧ P.count PrimitiveGate.T ≤ fieldMulTCost w := by
  sorry

/-!
## Spacetime Cost Target (`w = 256`)
-/

/-- Claimed spacetime cost (`T count * qubits`) of `fieldMulProgram` at bit length `256`. -/
def fieldMulW256ConstCost : ℕ := sorry

/-- For every modulus, `fieldMulProgram 256` uses no primitive `TOFF` gates and has spacetime cost
`T count * (3 * 256 + fieldMulAncillas 256)` at most `fieldMulW256ConstCost`, across all register
placements. -/
theorem fieldMul_w256_const_cost (p : ℕ) {n : ℕ}
    (rData : QRegister (3 * 256) n)
    (rAnc : QRegister (fieldMulAncillas 256) n) :
    let P := fieldMulProgram 256 p rData rAnc
    P.count PrimitiveGate.TOFF = 0 ∧
      P.count PrimitiveGate.T * (3 * 256 + fieldMulAncillas 256) ≤ fieldMulW256ConstCost := by
  sorry

end QuantumComputation.Specs
