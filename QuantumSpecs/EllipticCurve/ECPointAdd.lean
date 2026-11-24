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
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Algebra.Field.ZMod

/-!
# Affine Elliptic-Curve Point Addition of a Classical Point (`ecAdd`) Specification

Parameterized specification for in-place addition of a classical point to a quantum point on a
short Weierstrass curve `E : y² = x³ + a x + b` over a prime field `𝔽_p`, `p > 3`:
`|P⟩|0⟩^⊗m ↦ |P + Q⟩|0⟩^⊗m`, where `Q = (x_Q, y_Q)` is a classical affine point of `E` known when
the circuit is built, and `P = (x, y)` is an affine point of `E` held in `2 * w` data qubits. The
group law is Mathlib's `WeierstrassCurve.Affine.Point` addition, which is defined on the
nonsingular affine points and the point at infinity. The curve is not required to be elliptic: for
a singular curve the specification concerns its nonsingular points, and `Q` must be one of them.

Encoding: `w` is the bit length of `p` (`2^(w-1) < p < 2^w`). A point `(x, y)` is the
computational-basis index `x + 2^w * y` of the `2 * w`-qubit data register, with `x` and `y` the
standard representatives in `[0, p)`: the first `w` wires hold `x` and the last `w` wires hold `y`,
in the library's register convention (as in `Arcsin`, matching `finProdFinEquiv`).

Valid inputs are the nonsingular affine points of `E` with `x ≠ x_Q`. This excludes the point at
infinity (which has no affine encoding), `P = Q` (doubling) and `P = -Q` (sum at infinity), as in
the controlled point addition of Roetteler, Naehrig, Svore and Lauter (2017). On valid inputs the
sum is again an affine point and the map is injective, so it extends to a permutation of the basis.
The action on all other basis states is unconstrained, and inputs with nonzero ancillas are
unconstrained. The ancillas must be returned to zero.

The resource metric is the `T` count over Clifford + `T` with measurements, stated for every bit
length `w`, together with the spacetime (`T count * qubits`) at `w = 256`, where
`qubits = 2 * w + ecAddAncillas w` is the total number of data and clean ancilla qubits. `TOFF`
gates are excluded, so each Toffoli is costed by its Clifford + `T` construction, such as `4` `T`
gates with an ancilla and a measurement (C. Jones, Phys. Rev. A 87, 022328 (2013)). Clifford
gates, measurements and classical control are not counted, and the program has one classical
variable for measurement outcomes.

Both cost theorems carry no hypotheses: the bound depends only on `w` and must hold for every
natural number `p` (prime or not, of any size), all `a`, `b`, `x_Q`, `y_Q`, and every register
placement, while correctness is required only for primes `p > 3` of bit length `w`. So the bound is
a worst case over all primes, curves and points of that bit length, with no credit for a special
prime, and outside the correctness hypotheses the program may be anything that meets the bound,
such as the identity. The program may depend on `p`, `a`, `b` and `Q`; classical computation on
them is not costed. The `T`-count theorem does not bound qubits: a `T`-count claim is the pair
(`ecAddTCost w`, `2 * w + ecAddAncillas w`), and only the `w = 256` theorem combines the two into
one number. The claimed costs are upper bounds supplied by the solver; a smaller proved bound is a
better solution.

References:
- M. Roetteler, M. Naehrig, K. M. Svore, K. Lauter, "Quantum resource estimates for computing
  elliptic curve discrete logarithms", ASIACRYPT 2017, arXiv:1706.06752.
- T. Häner, S. Jaques, M. Naehrig, M. Roetteler, M. Soeken, "Improved quantum circuits for elliptic
  curve discrete logarithms", PQCrypto 2020, arXiv:2001.09580.
- D. Litinski, "How to compute a 256-bit elliptic curve private key with only 50 million Toffoli
  gates", arXiv:2306.08585.
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator WeierstrassCurve.Affine

/-!
## Curve, Encoding & Valid Inputs
-/

/-- The short Weierstrass curve `y² = x³ + a x + b` over `ZMod p`, in affine coordinates. -/
abbrev ecCurve {p : ℕ} (a b : ZMod p) : WeierstrassCurve.Affine (ZMod p) :=
  ⟨0, 0, 0, a, b⟩

/-- Basis index `(x + 2^w * y) mod 2^(2w)` of the `2 * w`-qubit data register encoding the affine
point `(x, y)`, with `x` and `y` the standard representatives in `[0, p)`. The reduction modulo
`2^(2w)` only makes the definition total: it does nothing when `p ≤ 2^w`. -/
def ecEncode (w : ℕ) {p : ℕ} (x y : ZMod p) : Fin (2 ^ (2 * w)) :=
  ⟨(x.val + 2 ^ w * y.val) % 2 ^ (2 * w), Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- Valid inputs: encodings of the affine points `(x, y)` of `ecCurve a b` with `x ≠ xQ`. -/
def ecAddValidInputs (w : ℕ) {p : ℕ} (a b xQ : ZMod p) : Set (Fin (2 ^ (2 * w))) :=
  {u | ∃ x y : ZMod p, (ecCurve a b).Nonsingular x y ∧ x ≠ xQ ∧ u = ecEncode w x y}

/-- A basis permutation `σ` agrees with addition of the classical point `Q = (xQ, yQ)` on valid
inputs: whenever `(x, y)` is an affine point with `x ≠ xQ` and `(x, y) + Q = (x', y')` in the
Mathlib group law, `σ` maps the encoding of `(x, y)` to the encoding of `(x', y')`. -/
def IsECAddPerm (w : ℕ) {p : ℕ} [Fact p.Prime] (a b xQ yQ : ZMod p)
    (hQ : (ecCurve a b).Nonsingular xQ yQ) (σ : Equiv.Perm (Fin (2 ^ (2 * w)))) : Prop :=
  ∀ (x y : ZMod p) (h : (ecCurve a b).Nonsingular x y), x ≠ xQ →
    ∀ (x' y' : ZMod p) (h' : (ecCurve a b).Nonsingular x' y'),
      Point.some x y h + Point.some xQ yQ hQ = Point.some x' y' h' →
        σ (ecEncode w x y) = ecEncode w x' y'

/-- Every valid input has an affine sum, so `IsECAddPerm` constrains `σ` on every valid input. -/
theorem ecAdd_sum_affine {p : ℕ} [Fact p.Prime] (a b xQ yQ : ZMod p)
    (hQ : (ecCurve a b).Nonsingular xQ yQ)
    (x y : ZMod p) (h : (ecCurve a b).Nonsingular x y) (hx : x ≠ xQ) :
    ∃ (x' y' : ZMod p) (h' : (ecCurve a b).Nonsingular x' y'),
      Point.some x y h + Point.some xQ yQ hQ = Point.some x' y' h' :=
  ⟨_, _, _, Point.add_of_X_ne hx⟩

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive ECPointAdd.Var where | v deriving DecidableEq, Inhabited

open ECPointAdd (Var)
open ECPointAdd.Var (v)

/-- Number of clean ancilla qubits `ecAddProgram` uses at bit length `w`. -/
def ecAddAncillas (w : ℕ) : ℕ := sorry

/-- Point-addition circuit for the classical point `(xQ, yQ)` on `ecCurve a b` over `ZMod p`, on
`2 * w` data wires `rData` (`w` wires for `x` followed by `w` wires for `y`) and `ecAddAncillas w`
clean ancilla wires `rAnc`. -/
def ecAddProgram {n : ℕ} (w p : ℕ) (a b xQ yQ : ZMod p)
    (rData : QRegister (2 * w) n)
    (rAnc : QRegister (ecAddAncillas w) n) : DynamicCircuit Var n :=
  sorry

/-- Parameterized correctness theorem: for a prime `p > 3` of bit length `w` and an affine point
`(xQ, yQ)` of `ecCurve a b`, there is a basis permutation `σ` that agrees with addition of
`(xQ, yQ)` on all valid inputs, and `ecAddProgram` realizes `σ` on valid inputs as a clean
subroutine across all disjoint register placements. -/
theorem ecAdd_correctness (w p : ℕ) [Fact p.Prime]
    (hp : 3 < p) (hlo : 2 ^ (w - 1) < p) (hhi : p < 2 ^ w)
    (a b xQ yQ : ZMod p) (hQ : (ecCurve a b).Nonsingular xQ yQ) :
    ∃ σ : Equiv.Perm (Fin (2 ^ (2 * w))),
      IsECAddPerm w a b xQ yQ hQ σ ∧
      ∀ {n : ℕ}
        (rData : QRegister (2 * w) n)
        (rAnc : QRegister (ecAddAncillas w) n)
        (hdisj : rData.DisjointWires rAnc),
        RealizesCleanSubroutineOnEncoding rData rAnc hdisj (ecAddValidInputs w a b xQ) σ
          (ecAddProgram w p a b xQ yQ rData rAnc).compile := by sorry

/-!
## `T`-Count Cost Target (all bit lengths)
-/

/-- Claimed `T` count of `ecAddProgram` at bit length `w`. -/
def ecAddTCost (w : ℕ) : ℕ := sorry

/-- For every modulus, curve and classical point, `ecAddProgram` uses no primitive `TOFF` gates and
at most `ecAddTCost w` `T` gates, across all register placements. -/
theorem ecAdd_t_cost (w p : ℕ) (a b xQ yQ : ZMod p) {n : ℕ}
    (rData : QRegister (2 * w) n)
    (rAnc : QRegister (ecAddAncillas w) n) :
    let P := ecAddProgram w p a b xQ yQ rData rAnc
    P.count PrimitiveGate.TOFF = 0 ∧ P.count PrimitiveGate.T ≤ ecAddTCost w := by
  sorry

/-!
## Spacetime Cost Target (`w = 256`)
-/

/-- Claimed spacetime cost (`T count * qubits`) of `ecAddProgram` at bit length `256`. -/
def ecAddW256ConstCost : ℕ := sorry

/-- For every modulus, curve and classical point, `ecAddProgram 256` uses no primitive `TOFF` gates
and has spacetime cost `T count * (2 * 256 + ecAddAncillas 256)` at most `ecAddW256ConstCost`,
across all register placements. -/
theorem ecAdd_w256_const_cost (p : ℕ) (a b xQ yQ : ZMod p) {n : ℕ}
    (rData : QRegister (2 * 256) n)
    (rAnc : QRegister (ecAddAncillas 256) n) :
    let P := ecAddProgram 256 p a b xQ yQ rData rAnc
    P.count PrimitiveGate.TOFF = 0 ∧
      P.count PrimitiveGate.T * (2 * 256 + ecAddAncillas 256) ≤ ecAddW256ConstCost := by
  sorry

end QuantumComputation.Specs
