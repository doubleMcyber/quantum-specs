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
# Projective Elliptic-Curve Point Addition of a Classical Point (`ecAddProj`) Specification

Parameterized specification for out-of-place mixed addition in homogeneous projective coordinates
on a short Weierstrass curve `E : y² = x³ + a x + b` over a prime field `𝔽_p`, `p > 3`:
`|X, Y, Z⟩|0, 0, 0⟩|0⟩^⊗m ↦ |X, Y, Z⟩|X', Y', Z'⟩|0⟩^⊗m`, where `(X : Y : Z)` with `Z ≠ 0`
represents the affine point `P = (X / Z, Y / Z)`, `Q = (x_Q, y_Q)` is a classical affine point of
`E` known when the circuit is built, and `(X' : Y' : Z')` with `Z' ≠ 0` represents `P + Q`. The
group law is Mathlib's `WeierstrassCurve.Affine.Point` addition on nonsingular points; the curve
is not required to be elliptic.

The output representative is the solver's choice: the correctness theorem asks for a table `f`
from input triples to output triples such that `f (X, Y, Z)` represents `P + Q` whenever
`(X, Y, Z)` represents a valid `P`, and for the program to write `f (X, Y, Z)` into the zeroed
output register. So an inversion-free formula and a normalized output (`Z' = 1`) are both
admissible, and the cost theorems decide between them. The table may depend on the
representative, not only on the point.

Encoding: `w` is the bit length of `p` (`2^(w-1) < p < 2^w`). The `2 * (3 * w)`-qubit data
register holds the input triple in its first `3 * w` wires and the output triple in its last
`3 * w` wires. A triple `(X, Y, Z)` is the index `X + 2^w * Y + 2^(2w) * Z` of its `3 * w` wires,
with standard representatives in `[0, p)`, least-significant wire first, in the library's register
convention.

Valid inputs: the input triple represents a nonsingular affine point `P` of `E` with
`x(P) ≠ x_Q`, and the output register is zero. This excludes the point at infinity (`Z = 0`),
doubling and `P = -Q`. The action on all other basis states is unconstrained, and inputs with
nonzero ancillas are unconstrained. The ancillas must be returned to zero.

The resource metric is the `T` count over Clifford + `T` with measurements, stated for every bit
length `w`, together with the spacetime (`T count * qubits`) at `w = 256`, where
`qubits = 2 * (3 * w) + ecAddProjAncillas w`. `TOFF` gates are excluded, so each Toffoli is costed
by its Clifford + `T` construction, such as `4` `T` gates with an ancilla and a measurement
(C. Jones, Phys. Rev. A 87, 022328 (2013)). Clifford gates, measurements and classical control are
not counted, and the program has one classical variable for measurement outcomes.

Both cost theorems carry no hypotheses: the bound depends only on `w` and must hold for every
natural number `p`, all `a`, `b`, `x_Q`, `y_Q`, and every register placement, while correctness is
required only for primes `p > 3` of bit length `w`. So the bound is a worst case over all primes,
curves and points of that bit length, and outside the correctness hypotheses the program may be
anything that meets the bound. The program may depend on `p`, `a`, `b` and `Q`; classical
computation on them is not costed. The `T`-count theorem does not bound qubits: a `T`-count claim
is the pair (`ecAddProjTCost w`, `2 * (3 * w) + ecAddProjAncillas w`). The claimed costs are upper
bounds supplied by the solver; a smaller proved bound is a better solution.

References:
- H. Cohen, A. Miyaji, T. Ono, "Efficient elliptic curve exponentiation using mixed coordinates",
  ASIACRYPT 1998.
- M. Roetteler, M. Naehrig, K. M. Svore, K. Lauter, "Quantum resource estimates for computing
  elliptic curve discrete logarithms", ASIACRYPT 2017, arXiv:1706.06752.
- T. Häner, S. Jaques, M. Naehrig, M. Roetteler, M. Soeken, "Improved quantum circuits for elliptic
  curve discrete logarithms", PQCrypto 2020, arXiv:2001.09580.
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator WeierstrassCurve.Affine

/-!
## Curve, Encoding & Valid Inputs
-/

/-- The short Weierstrass curve `y² = x³ + a x + b` over `ZMod p`, in affine coordinates. -/
abbrev ecProjCurve {p : ℕ} (a b : ZMod p) : WeierstrassCurve.Affine (ZMod p) :=
  ⟨0, 0, 0, a, b⟩

/-- A projective triple over `ZMod p`: `(X, Y, Z)`. -/
abbrev ProjTriple (p : ℕ) : Type := ZMod p × ZMod p × ZMod p

/-- The triple `T = (X, Y, Z)` represents the affine point `(x, y)`: `Z ≠ 0`, `X = x * Z` and
`Y = y * Z`. -/
def IsProjRep {p : ℕ} (T : ProjTriple p) (x y : ZMod p) : Prop :=
  T.2.2 ≠ 0 ∧ T.1 = x * T.2.2 ∧ T.2.1 = y * T.2.2

/-- Index `(X + 2^w * Y + 2^(2w) * Z) mod 2^(3w)` of the `3 * w` wires holding a triple. The
reduction only makes the definition total: it does nothing when `p ≤ 2^w`. -/
def ecProjEncode (w : ℕ) {p : ℕ} (T : ProjTriple p) : Fin (2 ^ (3 * w)) :=
  ⟨(T.1.val + 2 ^ w * T.2.1.val + 2 ^ (2 * w) * T.2.2.val) % 2 ^ (3 * w),
    Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- Index of the `2 * (3 * w)`-qubit data register holding the input triple `T` in its first
`3 * w` wires and the output triple `R` in its last `3 * w` wires. -/
def ecProjPairEncode (w : ℕ) {p : ℕ} (T R : ProjTriple p) : Fin (2 ^ (2 * (3 * w))) :=
  ⟨((ecProjEncode w T).val + 2 ^ (3 * w) * (ecProjEncode w R).val) % 2 ^ (2 * (3 * w)),
    Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- Valid inputs: the input triple represents a nonsingular affine point `(x, y)` of
`ecProjCurve a b` with `x ≠ xQ`, and the output triple is zero. -/
def ecAddProjValidInputs (w : ℕ) {p : ℕ} (a b xQ : ZMod p) : Set (Fin (2 ^ (2 * (3 * w)))) :=
  {u | ∃ (x y : ZMod p) (T : ProjTriple p), (ecProjCurve a b).Nonsingular x y ∧ x ≠ xQ ∧
    IsProjRep T x y ∧ u = ecProjPairEncode w T (0, 0, 0)}

/-- The table `f` computes addition of the classical point `Q = (xQ, yQ)`: whenever `T` represents
an affine point `(x, y)` with `x ≠ xQ` and `(x, y) + Q = (x', y')` in the Mathlib group law,
`f T` represents `(x', y')`. -/
def IsECAddProjTable {p : ℕ} [Fact p.Prime] (a b xQ yQ : ZMod p)
    (hQ : (ecProjCurve a b).Nonsingular xQ yQ) (f : ProjTriple p → ProjTriple p) : Prop :=
  ∀ (x y : ZMod p) (h : (ecProjCurve a b).Nonsingular x y), x ≠ xQ →
    ∀ T : ProjTriple p, IsProjRep T x y →
      ∀ (x' y' : ZMod p) (h' : (ecProjCurve a b).Nonsingular x' y'),
        Point.some x y h + Point.some xQ yQ hQ = Point.some x' y' h' →
          IsProjRep (f T) x' y'

/-- The basis permutation `σ` writes the table `f` into a zeroed output register on valid inputs:
it maps the encoding of `(T, 0)` to the encoding of `(T, f T)`. -/
def IsECAddProjPerm (w : ℕ) {p : ℕ} (a b xQ : ZMod p) (f : ProjTriple p → ProjTriple p)
    (σ : Equiv.Perm (Fin (2 ^ (2 * (3 * w))))) : Prop :=
  ∀ (x y : ZMod p), (ecProjCurve a b).Nonsingular x y → x ≠ xQ →
    ∀ T : ProjTriple p, IsProjRep T x y →
      σ (ecProjPairEncode w T (0, 0, 0)) = ecProjPairEncode w T (f T)

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive ECPointAddProj.Var where | v deriving DecidableEq, Inhabited

open ECPointAddProj (Var)
open ECPointAddProj.Var (v)

/-- Number of clean ancilla qubits `ecAddProjProgram` uses at bit length `w`. -/
def ecAddProjAncillas (w : ℕ) : ℕ := sorry

/-- Projective point-addition circuit for the classical point `(xQ, yQ)` on `ecProjCurve a b` over
`ZMod p`, on `2 * (3 * w)` data wires `rData` (input triple, then output triple) and
`ecAddProjAncillas w` clean ancilla wires `rAnc`. -/
def ecAddProjProgram {n : ℕ} (w p : ℕ) (a b xQ yQ : ZMod p)
    (rData : QRegister (2 * (3 * w)) n)
    (rAnc : QRegister (ecAddProjAncillas w) n) : DynamicCircuit Var n :=
  sorry

/-- Parameterized correctness theorem: for a prime `p > 3` of bit length `w` and an affine point
`(xQ, yQ)` of `ecProjCurve a b`, there are a table `f` computing addition of `(xQ, yQ)` on
projective representatives and a basis permutation `σ` writing `f` into a zeroed output register
on valid inputs, and `ecAddProjProgram` realizes `σ` on valid inputs as a clean subroutine across
all disjoint register placements. -/
theorem ecAddProj_correctness (w p : ℕ) [Fact p.Prime]
    (hp : 3 < p) (hlo : 2 ^ (w - 1) < p) (hhi : p < 2 ^ w)
    (a b xQ yQ : ZMod p) (hQ : (ecProjCurve a b).Nonsingular xQ yQ) :
    ∃ (f : ProjTriple p → ProjTriple p) (σ : Equiv.Perm (Fin (2 ^ (2 * (3 * w))))),
      IsECAddProjTable a b xQ yQ hQ f ∧
      IsECAddProjPerm w a b xQ f σ ∧
      ∀ {n : ℕ}
        (rData : QRegister (2 * (3 * w)) n)
        (rAnc : QRegister (ecAddProjAncillas w) n)
        (hdisj : rData.DisjointWires rAnc),
        RealizesCleanSubroutineOnEncoding rData rAnc hdisj (ecAddProjValidInputs w a b xQ) σ
          (ecAddProjProgram w p a b xQ yQ rData rAnc).compile := by sorry

/-!
## `T`-Count Cost Target (all bit lengths)
-/

/-- Claimed `T` count of `ecAddProjProgram` at bit length `w`. -/
def ecAddProjTCost (w : ℕ) : ℕ := sorry

/-- For every modulus, curve and classical point, `ecAddProjProgram` uses no primitive `TOFF` gates
and at most `ecAddProjTCost w` `T` gates, across all register placements. -/
theorem ecAddProj_t_cost (w p : ℕ) (a b xQ yQ : ZMod p) {n : ℕ}
    (rData : QRegister (2 * (3 * w)) n)
    (rAnc : QRegister (ecAddProjAncillas w) n) :
    let P := ecAddProjProgram w p a b xQ yQ rData rAnc
    P.count PrimitiveGate.TOFF = 0 ∧ P.count PrimitiveGate.T ≤ ecAddProjTCost w := by
  sorry

/-!
## Spacetime Cost Target (`w = 256`)
-/

/-- Claimed spacetime cost (`T count * qubits`) of `ecAddProjProgram` at bit length `256`. -/
def ecAddProjW256ConstCost : ℕ := sorry

/-- For every modulus, curve and classical point, `ecAddProjProgram 256` uses no primitive `TOFF`
gates and has spacetime cost `T count * (2 * (3 * 256) + ecAddProjAncillas 256)` at most
`ecAddProjW256ConstCost`, across all register placements. -/
theorem ecAddProj_w256_const_cost (p : ℕ) (a b xQ yQ : ZMod p) {n : ℕ}
    (rData : QRegister (2 * (3 * 256)) n)
    (rAnc : QRegister (ecAddProjAncillas 256) n) :
    let P := ecAddProjProgram 256 p a b xQ yQ rData rAnc
    P.count PrimitiveGate.TOFF = 0 ∧
      P.count PrimitiveGate.T * (2 * (3 * 256) + ecAddProjAncillas 256) ≤
        ecAddProjW256ConstCost := by
  sorry

end QuantumComputation.Specs
