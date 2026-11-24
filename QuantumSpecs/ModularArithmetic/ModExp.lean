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
# Modular Exponentiation (`modExp`) Specification

Parameterized specification for the exact reversible modular exponentiation of Shor's algorithm,
with a quantum exponent and a classical base and modulus:
`|e⟩|y⟩|0⟩^⊗m ↦ |e⟩|g^e * y mod N⟩|0⟩^⊗m` for every `ℓ`-bit exponent `e` and every
`y ∈ [0, N)`, where `y` is a `b`-bit unsigned integer, `1 ≤ N ≤ 2^b`, and `gcd(g, N) = 1`.
Running it on `|e⟩|1⟩` gives `|e⟩|g^e mod N⟩`. The base `g` and modulus `N` are classical
parameters of the program (known when the circuit is built). Basis states with `y ≥ N` are
invalid encodings and their image is unconstrained.

(P. W. Shor, SIAM J. Comput. 26, 1484 (1997); M. Ekerå and J. Håstad, PQCrypto 2017;
C. Gidney, arXiv:2505.15917 (2025).)

The map is exact. Approximate constructions such as the approximate residue-arithmetic
exponentiation of Gidney (2025), whose output is correct only up to a bounded error, do not
satisfy this specification; their cost is therefore not a baseline for it.

The resource metrics are counted over Clifford + `T` with measurements, with `TOFF` gates
excluded. Qubits are `p.ℓ + p.b + modExpAncillas p`, the data and clean ancilla qubits. Two cost
claims are frozen at the RSA-2048 width `b = 2048` with an `ℓ = 1280`-bit exponent register (the
input register length of Gidney 2025, Table 5, `n = 2048` row), each uniformly over every modulus
`N ≤ 2^2048` and every base `g` coprime to `N`: the spacetime cost `T count * qubits`, and the
`T` count alone.
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator

/-- Widths, modulus and base: `ℓ`-bit exponent register, `b`-bit target register, classical
modulus `1 ≤ N ≤ 2^b`, classical base `g` coprime to `N`. -/
structure ModExpParams where
  /-- Exponent register bit-width `ℓ`. -/
  ℓ : ℕ
  /-- Target register bit-width `b`. -/
  b : ℕ
  /-- Classical modulus `N`. -/
  N : ℕ
  /-- Classical base `g`. -/
  g : ℕ
  /-- The modulus is positive. -/
  hN : 0 < N
  /-- The modulus fits in `b` bits. -/
  hNb : N ≤ 2 ^ b
  /-- The base is invertible modulo `N`. -/
  hcop : Nat.Coprime g N

/-!
## Residue Encoding and the Exponentiation Permutation
-/

/-- `b`-bit basis indices below `N`, identified with `Fin N`. -/
def ModExpParams.residueEquiv (p : ModExpParams) :
    Fin p.N ≃ {y : Fin (2 ^ p.b) // (y : ℕ) < p.N} where
  toFun i := ⟨⟨i, lt_of_lt_of_le i.isLt p.hNb⟩, i.isLt⟩
  invFun y := ⟨y.1, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Residue map `y ↦ g^e * y mod N` for a classical exponent `e`. -/
def modExpMulFun (p : ModExpParams) (e : ℕ) (y : Fin p.N) : Fin p.N :=
  ⟨p.g ^ e * y % p.N, Nat.mod_lt _ p.hN⟩

theorem modExpMulFun_injective (p : ModExpParams) (e : ℕ) :
    Function.Injective (modExpMulFun p e) := by
  intro x y h
  have h' : p.g ^ e * x ≡ p.g ^ e * y [MOD p.N] := congrArg Fin.val h
  have h'' := Nat.ModEq.cancel_left_div_gcd p.hN h'
  rw [Nat.gcd_comm, Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left e p.hcop), Nat.div_one] at h''
  exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt h'' x.isLt y.isLt)

/-- Basis permutation of the target register for a classical exponent `e`:
`y ↦ g^e * y mod N` on residues `y < N`, fixing every `y ≥ N`. -/
noncomputable def modExpMulPerm (p : ModExpParams) (e : ℕ) : Equiv.Perm (Fin (2 ^ p.b)) :=
  Equiv.Perm.extendDomain
    (Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (modExpMulFun_injective p e)))
    p.residueEquiv

/-- Basis permutation on `Fin (2 ^ (p.ℓ + p.b))` for `|e⟩|y⟩ ↦ |e⟩|g^e * y mod N⟩`, with the
pair `(e, y)` read by `splitBasisEquiv`. Only valid inputs (`y < N`) are constrained by the
correctness theorem. -/
noncomputable def modExpPerm (p : ModExpParams) : Equiv.Perm (Fin (2 ^ (p.ℓ + p.b))) :=
  (splitBasisEquiv p.ℓ p.b).trans
    ((Equiv.prodShear (Equiv.refl _) fun e ↦ modExpMulPerm p e.val).trans
      (splitBasisEquiv p.ℓ p.b).symm)

/-- Valid inputs: any exponent `e`, and the target holds a residue, `y < N`. -/
def modExpValidInputs (p : ModExpParams) : Set (Fin (2 ^ (p.ℓ + p.b))) :=
  {i | ((splitBasisEquiv p.ℓ p.b i).2 : ℕ) < p.N}

/-- On valid inputs, `modExpPerm` is `(e, y) ↦ (e, g^e * y mod N)`. -/
theorem modExpPerm_apply_valid (p : ModExpParams) (e : Fin (2 ^ p.ℓ)) (y : Fin (2 ^ p.b))
    (hy : (y : ℕ) < p.N) :
    splitBasisEquiv p.ℓ p.b (modExpPerm p ((splitBasisEquiv p.ℓ p.b).symm (e, y))) =
      (e, ⟨p.g ^ (e : ℕ) * y % p.N, lt_of_lt_of_le (Nat.mod_lt _ p.hN) p.hNb⟩) := by
  simp only [modExpPerm, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.prodShear_apply,
    Equiv.refl_apply, Prod.mk.injEq, true_and]
  rw [modExpMulPerm, Equiv.Perm.extendDomain_apply_subtype _ p.residueEquiv (b := y) hy]
  rfl

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive ModExp.Var where | v deriving DecidableEq, Inhabited

open ModExp (Var)

/-- Number of clean ancilla qubits `modExpProgram` uses for parameters `p`. -/
def modExpAncillas (p : ModExpParams) : ℕ := sorry

/-- Parameterized modular-exponentiation circuit on `p.ℓ + p.b` data wires `rData` (`p.b` target
wires `y` followed by `p.ℓ` exponent wires `e`, each little-endian, matching `finProdFinEquiv`
as in `tableAddPerm`) and `modExpAncillas p` clean ancilla wires `rAnc`. -/
def modExpProgram {n : ℕ} (p : ModExpParams)
    (rData : QRegister (p.ℓ + p.b) n)
    (rAnc : QRegister (modExpAncillas p) n) : DynamicCircuit Var n :=
  sorry

/-- Parameterized correctness theorem: for all widths, modulus `1 ≤ N ≤ 2^b` and base `g`
coprime to `N`, `modExpProgram p` maps every valid input `|e⟩|y⟩` (`y < N`) with clean ancillas
to `|e⟩|g^e * y mod N⟩` with clean ancillas, across all disjoint register placements. -/
theorem modExp_correctness (p : ModExpParams) :
    ∀ {n : ℕ}
      (rData : QRegister (p.ℓ + p.b) n)
      (rAnc : QRegister (modExpAncillas p) n)
      (hdisj : rData.DisjointWires rAnc),
      RealizesCleanSubroutineOnEncoding rData rAnc hdisj (modExpValidInputs p) (modExpPerm p)
        (modExpProgram p rData rAnc).compile := by sorry

/-- `T`-gate count of `modExpProgram p`. -/
abbrev modExpTCount {n : ℕ} (p : ModExpParams)
    (rData : QRegister (p.ℓ + p.b) n)
    (rAnc : QRegister (modExpAncillas p) n) : ℕ :=
  (modExpProgram p rData rAnc).count PrimitiveGate.T

/-- Spacetime cost `T count * qubits` of `modExpProgram p`, counting all
`p.ℓ + p.b + modExpAncillas p` data and clean ancilla qubits. -/
abbrev modExpSpacetime {n : ℕ} (p : ModExpParams)
    (rData : QRegister (p.ℓ + p.b) n)
    (rAnc : QRegister (modExpAncillas p) n) : ℕ :=
  modExpTCount p rData rAnc * (p.ℓ + p.b + modExpAncillas p)

/-!
## Cost Theorems

Both forbid primitive `TOFF` gates and hold uniformly over every modulus and every coprime base
at `ℓ = 1280`, `b = 2048`.
-/

/-- At widths `ℓ` and `b`, for every modulus and coprime base, `modExpProgram` uses no primitive
`TOFF` gates and has spacetime cost at most `cost` across all register placements. -/
abbrev SatisfiesModExpSpacetimeBound (ℓ b cost : ℕ) : Prop :=
  ∀ (p : ModExpParams), p.ℓ = ℓ → p.b = b →
    ∀ {n : ℕ}
      (rData : QRegister (p.ℓ + p.b) n)
      (rAnc : QRegister (modExpAncillas p) n),
      (modExpProgram p rData rAnc).count PrimitiveGate.TOFF = 0 ∧
        modExpSpacetime p rData rAnc ≤ cost

/-- At widths `ℓ` and `b`, for every modulus and coprime base, `modExpProgram` uses no primitive
`TOFF` gates and at most `cost` `T` gates across all register placements. -/
abbrev SatisfiesModExpTCountBound (ℓ b cost : ℕ) : Prop :=
  ∀ (p : ModExpParams), p.ℓ = ℓ → p.b = b →
    ∀ {n : ℕ}
      (rData : QRegister (p.ℓ + p.b) n)
      (rAnc : QRegister (modExpAncillas p) n),
      (modExpProgram p rData rAnc).count PrimitiveGate.TOFF = 0 ∧
        modExpTCount p rData rAnc ≤ cost

/-- Claimed spacetime cost bound at `ℓ = 1280`, `b = 2048`. -/
def modExpL1280B2048SpacetimeCost : ℕ := sorry

theorem modExp_l1280_b2048_spacetime_cost :
    SatisfiesModExpSpacetimeBound 1280 2048 modExpL1280B2048SpacetimeCost := by sorry

/-- Claimed `T`-count bound at `ℓ = 1280`, `b = 2048`. -/
def modExpL1280B2048TCountCost : ℕ := sorry

theorem modExp_l1280_b2048_t_count_cost :
    SatisfiesModExpTCountBound 1280 2048 modExpL1280B2048TCountCost := by sorry

end QuantumComputation.Specs
