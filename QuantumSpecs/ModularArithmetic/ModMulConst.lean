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
# Modular Multiplication by a Classical Constant (`modMulConst`) Specification

Parameterized specification for reversible in-place multiplication of a quantum register by a
classical constant `a` modulo a classical modulus `N`:
`|x⟩|0⟩^⊗m ↦ |a * x mod N⟩|0⟩^⊗m` for all `x ∈ [0, N)`,
where `x` is a `b`-bit unsigned integer, `1 ≤ N ≤ 2^b`, and `gcd(a, N) = 1`, so that
`x ↦ a * x mod N` is a permutation of the residues. Both `a` and `N` are classical parameters of
the program (known when the circuit is built). Basis states with `x ≥ N` are invalid encodings
and their image is unconstrained.

This is the controlled-free core of the modular-exponentiation step in Shor's algorithm
(S. Beauregard, Quantum Inf. Comput. 3, 175 (2003); C. Gidney, arXiv:1904.07356 (2019)).

The resource metrics are counted over Clifford + `T` with measurements, with `TOFF` gates
excluded. Qubits are `p.b + modMulConstAncillas p`, the data and clean ancilla qubits. Two cost
claims are frozen at the RSA-2048 width `b = 2048`, each uniformly over every modulus
`N ≤ 2^2048` and every multiplier `a` coprime to `N`: the spacetime cost `T count * qubits`,
and the `T` count alone.
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator

/-- Width, modulus and multiplier: `b`-bit register, classical modulus `1 ≤ N ≤ 2^b`, classical
multiplier `a` coprime to `N`. -/
structure ModMulConstParams where
  /-- Register bit-width `b`. -/
  b : ℕ
  /-- Classical modulus `N`. -/
  N : ℕ
  /-- Classical multiplier `a`. -/
  a : ℕ
  /-- The modulus is positive. -/
  hN : 0 < N
  /-- The modulus fits in `b` bits. -/
  hNb : N ≤ 2 ^ b
  /-- The multiplier is invertible modulo `N`. -/
  hcop : Nat.Coprime a N

/-!
## Residue Encoding and the Multiplication Permutation
-/

/-- `b`-bit basis indices below `N`, identified with `Fin N`. -/
def ModMulConstParams.residueEquiv (p : ModMulConstParams) :
    Fin p.N ≃ {x : Fin (2 ^ p.b) // (x : ℕ) < p.N} where
  toFun i := ⟨⟨i, lt_of_lt_of_le i.isLt p.hNb⟩, i.isLt⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Residue map `x ↦ a * x mod N`. -/
def modMulConstFun (p : ModMulConstParams) (x : Fin p.N) : Fin p.N :=
  ⟨p.a * x % p.N, Nat.mod_lt _ p.hN⟩

theorem modMulConstFun_injective (p : ModMulConstParams) :
    Function.Injective (modMulConstFun p) := by
  intro x y h
  have h' : p.a * x ≡ p.a * y [MOD p.N] := congrArg Fin.val h
  have h'' := Nat.ModEq.cancel_left_div_gcd p.hN h'
  rw [Nat.gcd_comm, Nat.Coprime.gcd_eq_one p.hcop, Nat.div_one] at h''
  exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt h'' x.isLt y.isLt)

/-- Basis permutation of the `b`-bit register: `x ↦ a * x mod N` on residues `x < N`, fixing
every `x ≥ N`. Only valid inputs are constrained by the correctness theorem. -/
noncomputable def modMulConstPerm (p : ModMulConstParams) : Equiv.Perm (Fin (2 ^ p.b)) :=
  Equiv.Perm.extendDomain
    (Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (modMulConstFun_injective p)))
    p.residueEquiv

/-- Valid inputs: the register holds a residue, `x < N`. -/
def modMulConstValidInputs (p : ModMulConstParams) : Set (Fin (2 ^ p.b)) :=
  {x | (x : ℕ) < p.N}

/-- On valid inputs, `modMulConstPerm` is `x ↦ a * x mod N`. -/
theorem modMulConstPerm_apply_valid (p : ModMulConstParams) (x : Fin (2 ^ p.b))
    (hx : (x : ℕ) < p.N) :
    ((modMulConstPerm p x : Fin (2 ^ p.b)) : ℕ) = p.a * x % p.N := by
  rw [modMulConstPerm, Equiv.Perm.extendDomain_apply_subtype _ p.residueEquiv (b := x) hx]
  rfl

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive ModMulConst.Var where | v deriving DecidableEq, Inhabited

open ModMulConst (Var)

/-- Number of clean ancilla qubits `modMulConstProgram` uses for parameters `p`. -/
def modMulConstAncillas (p : ModMulConstParams) : ℕ := sorry

/-- Parameterized circuit on `p.b` data wires `rData` (little-endian `x`) and
`modMulConstAncillas p` clean ancilla wires `rAnc`. -/
def modMulConstProgram {n : ℕ} (p : ModMulConstParams)
    (rData : QRegister p.b n)
    (rAnc : QRegister (modMulConstAncillas p) n) : DynamicCircuit Var n :=
  sorry

/-- Parameterized correctness theorem: for every width, modulus `1 ≤ N ≤ 2^b` and multiplier
`a` coprime to `N`, `modMulConstProgram p` maps every valid input `|x⟩` (`x < N`) with clean
ancillas to `|a * x mod N⟩` with clean ancillas, across all disjoint register placements. -/
theorem modMulConst_correctness (p : ModMulConstParams) :
    ∀ {n : ℕ}
      (rData : QRegister p.b n)
      (rAnc : QRegister (modMulConstAncillas p) n)
      (hdisj : rData.DisjointWires rAnc),
      RealizesCleanSubroutineOnEncoding rData rAnc hdisj (modMulConstValidInputs p)
        (modMulConstPerm p) (modMulConstProgram p rData rAnc).compile := by sorry

/-- `T`-gate count of `modMulConstProgram p`. -/
abbrev modMulConstTCount {n : ℕ} (p : ModMulConstParams)
    (rData : QRegister p.b n)
    (rAnc : QRegister (modMulConstAncillas p) n) : ℕ :=
  (modMulConstProgram p rData rAnc).count PrimitiveGate.T

/-- Spacetime cost `T count * qubits` of `modMulConstProgram p`, counting all
`p.b + modMulConstAncillas p` data and clean ancilla qubits. -/
abbrev modMulConstSpacetime {n : ℕ} (p : ModMulConstParams)
    (rData : QRegister p.b n)
    (rAnc : QRegister (modMulConstAncillas p) n) : ℕ :=
  modMulConstTCount p rData rAnc * (p.b + modMulConstAncillas p)

/-!
## Cost Theorems

Both forbid primitive `TOFF` gates and hold uniformly over every modulus and every coprime
multiplier at width `b = 2048`.
-/

/-- At width `b`, for every modulus and coprime multiplier, `modMulConstProgram` uses no
primitive `TOFF` gates and has spacetime cost at most `cost` across all register placements. -/
abbrev SatisfiesModMulConstSpacetimeBound (b cost : ℕ) : Prop :=
  ∀ (p : ModMulConstParams), p.b = b →
    ∀ {n : ℕ}
      (rData : QRegister p.b n)
      (rAnc : QRegister (modMulConstAncillas p) n),
      (modMulConstProgram p rData rAnc).count PrimitiveGate.TOFF = 0 ∧
        modMulConstSpacetime p rData rAnc ≤ cost

/-- At width `b`, for every modulus and coprime multiplier, `modMulConstProgram` uses no
primitive `TOFF` gates and at most `cost` `T` gates across all register placements. -/
abbrev SatisfiesModMulConstTCountBound (b cost : ℕ) : Prop :=
  ∀ (p : ModMulConstParams), p.b = b →
    ∀ {n : ℕ}
      (rData : QRegister p.b n)
      (rAnc : QRegister (modMulConstAncillas p) n),
      (modMulConstProgram p rData rAnc).count PrimitiveGate.TOFF = 0 ∧
        modMulConstTCount p rData rAnc ≤ cost

/-- Claimed spacetime cost bound at `b = 2048`. -/
def modMulConstB2048SpacetimeCost : ℕ := sorry

theorem modMulConst_b2048_spacetime_cost :
    SatisfiesModMulConstSpacetimeBound 2048 modMulConstB2048SpacetimeCost := by sorry

/-- Claimed `T`-count bound at `b = 2048`. -/
def modMulConstB2048TCountCost : ℕ := sorry

theorem modMulConst_b2048_t_count_cost :
    SatisfiesModMulConstTCountBound 2048 modMulConstB2048TCountCost := by sorry

end QuantumComputation.Specs
