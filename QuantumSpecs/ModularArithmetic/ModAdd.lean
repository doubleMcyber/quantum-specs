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
# Modular Addition (`modAdd`) Specification

Parameterized specification for reversible in-place modular addition of two quantum registers
modulo a classical modulus `N`:
`|x⟩|y⟩|0⟩^⊗m ↦ |x⟩|(x + y) mod N⟩|0⟩^⊗m` for all `x, y ∈ [0, N)`,
where `x` and `y` are `b`-bit unsigned integers and `1 ≤ N ≤ 2^b`. The modulus `N` is a
classical parameter of the program (known when the circuit is built), as in every factoring
construction. Basis states with `x ≥ N` or `y ≥ N` are invalid encodings and their image is
unconstrained.

This is the basic step of modular multiplication and exponentiation in Shor's algorithm
(V. Vedral, A. Barenco, A. Ekert, Phys. Rev. A 54, 147 (1996); S. Beauregard, Quantum Inf.
Comput. 3, 175 (2003); C. Gidney, Quantum 2, 74 (2018); C. Gidney, arXiv:2505.15917 (2025)).

The resource metrics are counted over Clifford + `T` with measurements, with `TOFF` gates
excluded, so each Toffoli is costed by its Clifford + `T` construction (for example `4` `T`
gates with an ancilla and a measurement-based uncompute, C. Jones, Phys. Rev. A 87, 022328
(2013)). Qubits are `2 * p.b + modAddAncillas p`, the data and clean ancilla qubits. Two cost
claims are frozen at the RSA-2048 width `b = 2048`, each uniformly over every modulus
`N ≤ 2^2048`: the spacetime cost `T count * qubits`, and the `T` count alone.
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator

/-- Width and modulus for modular addition: `b`-bit registers, classical modulus
`1 ≤ N ≤ 2^b`. -/
structure ModAddParams where
  /-- Register bit-width `b`. -/
  b : ℕ
  /-- Classical modulus `N`. -/
  N : ℕ
  /-- The modulus is positive. -/
  hN : 0 < N
  /-- The modulus fits in `b` bits: every residue `0 ≤ r < N` is a `b`-bit value. -/
  hNb : N ≤ 2 ^ b

/-!
## Residue Encoding and the Modular-Addition Permutation
-/

/-- `b`-bit basis indices below `N`, identified with `Fin N`. -/
def ModAddParams.residueEquiv (p : ModAddParams) :
    Fin p.N ≃ {y : Fin (2 ^ p.b) // (y : ℕ) < p.N} where
  toFun i := ⟨⟨i, lt_of_lt_of_le i.isLt p.hNb⟩, i.isLt⟩
  invFun y := ⟨y.1, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Basis permutation of one `b`-bit register adding `a mod N` to residues `y < N`
(`y ↦ (y + a) mod N`) and fixing every `y ≥ N`. -/
def modAddConstPerm (p : ModAddParams) (a : ℕ) : Equiv.Perm (Fin (2 ^ p.b)) :=
  haveI : NeZero p.N := ⟨p.hN.ne'⟩
  (Equiv.addRight (⟨a % p.N, Nat.mod_lt _ p.hN⟩ : Fin p.N)).extendDomain p.residueEquiv

/-- Basis permutation on `Fin (2 ^ (2 * p.b))` for in-place modular addition
`|x⟩|y⟩ ↦ |x⟩|(x + y) mod N⟩`, with the pair `(x, y)` read by `splitEqualBasisEquiv`.
Values `y ≥ N` are fixed; `x ≥ N` acts as `x mod N`. Only valid inputs (`x, y < N`) are
constrained by the correctness theorem. -/
def modAddPerm (p : ModAddParams) : Equiv.Perm (Fin (2 ^ (2 * p.b))) :=
  (splitEqualBasisEquiv p.b).trans
    ((Equiv.prodShear (Equiv.refl _) fun x ↦ modAddConstPerm p x.val).trans
      (splitEqualBasisEquiv p.b).symm)

/-- Valid inputs: both registers hold residues, `x < N` and `y < N`. -/
def modAddValidInputs (p : ModAddParams) : Set (Fin (2 ^ (2 * p.b))) :=
  {i | ((splitEqualBasisEquiv p.b i).1 : ℕ) < p.N ∧ ((splitEqualBasisEquiv p.b i).2 : ℕ) < p.N}

/-- On valid inputs, `modAddPerm` is `(x, y) ↦ (x, (x + y) mod N)`. -/
theorem modAddPerm_apply_valid (p : ModAddParams) (x y : Fin (2 ^ p.b))
    (hx : (x : ℕ) < p.N) (hy : (y : ℕ) < p.N) :
    splitEqualBasisEquiv p.b (modAddPerm p ((splitEqualBasisEquiv p.b).symm (x, y))) =
      (x, ⟨((x : ℕ) + y) % p.N, lt_of_lt_of_le (Nat.mod_lt _ p.hN) p.hNb⟩) := by
  have : NeZero p.N := ⟨p.hN.ne'⟩
  simp only [modAddPerm, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.prodShear_apply,
    Equiv.refl_apply, Prod.mk.injEq, true_and]
  rw [modAddConstPerm, Equiv.Perm.extendDomain_apply_subtype _ p.residueEquiv (b := y) hy]
  apply Fin.ext
  simp [ModAddParams.residueEquiv, Fin.val_add, Nat.mod_eq_of_lt hx, Nat.add_comm]

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive ModAdd.Var where | v deriving DecidableEq, Inhabited

open ModAdd (Var)

/-- Number of clean ancilla qubits `modAddProgram` uses for parameters `p`. -/
def modAddAncillas (p : ModAddParams) : ℕ := sorry

/-- Parameterized modular-addition circuit on `2 * p.b` data wires `rData` (`p.b` target wires
`y` followed by `p.b` source wires `x`, matching `finProdFinEquiv` as in `equalTableAddPerm`)
and `modAddAncillas p` clean ancilla wires `rAnc`. -/
def modAddProgram {n : ℕ} (p : ModAddParams)
    (rData : QRegister (2 * p.b) n)
    (rAnc : QRegister (modAddAncillas p) n) : DynamicCircuit Var n :=
  sorry

/-- Parameterized correctness theorem: for every width and modulus `1 ≤ N ≤ 2^b`,
`modAddProgram p` maps every valid input `|x⟩|y⟩` (`x, y < N`) with clean ancillas to
`|x⟩|(x + y) mod N⟩` with clean ancillas, across all disjoint register placements. -/
theorem modAdd_correctness (p : ModAddParams) :
    ∀ {n : ℕ}
      (rData : QRegister (2 * p.b) n)
      (rAnc : QRegister (modAddAncillas p) n)
      (hdisj : rData.DisjointWires rAnc),
      RealizesCleanSubroutineOnEncoding rData rAnc hdisj (modAddValidInputs p) (modAddPerm p)
        (modAddProgram p rData rAnc).compile := by sorry

/-- `T`-gate count of `modAddProgram p`. -/
abbrev modAddTCount {n : ℕ} (p : ModAddParams)
    (rData : QRegister (2 * p.b) n)
    (rAnc : QRegister (modAddAncillas p) n) : ℕ :=
  (modAddProgram p rData rAnc).count PrimitiveGate.T

/-- Spacetime cost `T count * qubits` of `modAddProgram p`, counting all
`2 * p.b + modAddAncillas p` data and clean ancilla qubits. -/
abbrev modAddSpacetime {n : ℕ} (p : ModAddParams)
    (rData : QRegister (2 * p.b) n)
    (rAnc : QRegister (modAddAncillas p) n) : ℕ :=
  modAddTCount p rData rAnc * (2 * p.b + modAddAncillas p)

/-!
## Cost Theorems

Both forbid primitive `TOFF` gates and hold uniformly over every modulus at width `b = 2048`.
-/

/-- At width `b`, for every modulus, `modAddProgram` uses no primitive `TOFF` gates and has
spacetime cost at most `cost` across all register placements. -/
abbrev SatisfiesModAddSpacetimeBound (b cost : ℕ) : Prop :=
  ∀ (p : ModAddParams), p.b = b →
    ∀ {n : ℕ}
      (rData : QRegister (2 * p.b) n)
      (rAnc : QRegister (modAddAncillas p) n),
      (modAddProgram p rData rAnc).count PrimitiveGate.TOFF = 0 ∧
        modAddSpacetime p rData rAnc ≤ cost

/-- At width `b`, for every modulus, `modAddProgram` uses no primitive `TOFF` gates and at
most `cost` `T` gates across all register placements. -/
abbrev SatisfiesModAddTCountBound (b cost : ℕ) : Prop :=
  ∀ (p : ModAddParams), p.b = b →
    ∀ {n : ℕ}
      (rData : QRegister (2 * p.b) n)
      (rAnc : QRegister (modAddAncillas p) n),
      (modAddProgram p rData rAnc).count PrimitiveGate.TOFF = 0 ∧
        modAddTCount p rData rAnc ≤ cost

/-- Claimed spacetime cost bound at `b = 2048`. -/
def modAddB2048SpacetimeCost : ℕ := sorry

theorem modAdd_b2048_spacetime_cost :
    SatisfiesModAddSpacetimeBound 2048 modAddB2048SpacetimeCost := by sorry

/-- Claimed `T`-count bound at `b = 2048`. -/
def modAddB2048TCountCost : ℕ := sorry

theorem modAdd_b2048_t_count_cost :
    SatisfiesModAddTCountBound 2048 modAddB2048TCountCost := by sorry

end QuantumComputation.Specs
