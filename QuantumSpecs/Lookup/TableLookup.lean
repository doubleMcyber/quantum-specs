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
public import QuantumComputation.Maths.Basis

/-!
# Table Lookup (`QROM`) and Measurement-Based Unlookup Specification

Parameterized specifications for loading classical data indexed by a quantum register: lookup
and unlookup, each also in a budgeted form whose clean-ancilla budget `a` is a size parameter
(the select-swap trade-off; see the section on budgets below).

**Lookup.** For a classical table `data : Fin L → Fin (2^w)` of `L ≤ 2^m` words of `w` bits,
realize `|x⟩|b⟩|0⟩^⊗a ↦ |x⟩|b ⊕ data(x)⟩|0⟩^⊗a` for every address `x < L` and every `w`-bit
target value `b`, where `⊕` is bitwise XOR. Addresses `x ≥ L` are unconstrained. The table is a
classical parameter of the program, so classical preprocessing of the table is free, as it is
for every quantum read-only memory construction in the literature.

**Unlookup.** For the same table, realize `|x⟩|data(x)⟩|0⟩^⊗a ↦ |x⟩|0⟩|0⟩^⊗a` for every address
`x < L`. Only inputs whose target already holds `data(x)` are constrained, so mid-circuit
measurement of the target followed by a classically controlled phase correction is allowed
(measurement-based uncomputation).

**Encoding.** The data register has `m + w` wires. Logical wire `0` is the least-significant bit
(library convention). Wires `0, ..., w - 1` hold the target `b` and wires `w, ..., w + m - 1`
hold the address `x`, matching `splitBasisEquiv m w` (index `b + 2^w * x`). Bit `i` of a word is
the radix-two digit `⌊b / 2^i⌋ mod 2` (`basisBits`).

**Resources.** Gates are Clifford + `T` with measurements and classical control. `TOFF` gates
are excluded, so each Toffoli is costed by its Clifford + `T` construction, such as `4` `T` gates
with an ancilla and a measurement (C. Jones, Phys. Rev. A 87, 022328 (2013)). Each spec has two
cost theorems, both for all sizes and all tables: a `T` count bound, and a spacetime bound
`T count * qubits` with `qubits = m + w + ancillas` (the data register plus the clean ancillas).
Each spec also has a pinned-size theorem at `LookupParams.l1024w32` (`L = 1024` entries of
`w = 32` bits, `m = 10`) that bounds `T count * qubits` by a closed constant, so a record at that
size is a single number.

**Reference baselines** (UNPROVED in Lean here; the record to beat):
* Lookup by unary iteration: `L - 1` Toffolis, so `4L - 4` `T` gates, with about `m` ancillas.
  R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, H. Neven,
  "Encoding electronic spectra in quantum circuits with linear T complexity",
  Phys. Rev. X 8, 041015 (2018), arXiv:1805.03662.
* Lookup by select-swap: fewer `T` gates at the cost of `λ w` extra qubits. G. H. Low,
  V. Kliuchnikov, L. Schaeffer, "Trading T-gates for dirty qubits in state preparation and
  unitary synthesis", arXiv:1812.00954.
* Unlookup by measurement-based uncomputation: about `L / k + k` Toffolis for a free choice of
  `k`. D. W. Berry, C. Gidney, M. Motta, J. R. McClean, R. Babbush, "Qubitization of arbitrary
  basis quantum chemistry leveraging sparsity and low rank factorization", Quantum 3, 208 (2019),
  arXiv:1902.02134, Appendix C; C. Gidney, "Windowed quantum arithmetic", arXiv:1905.07682.
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator

/-- Sizes of a table lookup. -/
structure LookupParams where
  /-- Number of table entries `L`. -/
  L : ℕ
  /-- Address register width `m`. -/
  m : ℕ
  /-- Word width `w` of each entry. -/
  w : ℕ

/-- The sizes are meaningful: at least one entry, and every entry is addressable. -/
def LookupParams.Valid (p : LookupParams) : Prop :=
  0 < p.L ∧ p.L ≤ 2 ^ p.m

/-- A classical table of `p.L` words of `p.w` bits. -/
abbrev LookupTable (p : LookupParams) : Type := Fin p.L → Fin (2 ^ p.w)

/-- The table extended to all `2^m` addresses, with `0` at addresses `x ≥ L`. The value outside
the table never enters a constrained input of either spec. -/
def LookupTable.extend {p : LookupParams} (data : LookupTable p) :
    Fin (2 ^ p.m) → Fin (2 ^ p.w) :=
  fun x ↦ if h : x.val < p.L then data ⟨x.val, h⟩ else 0

/-!
## Bitwise XOR and the Ideal Basis Permutation
-/

/-- Bitwise XOR with the constant `c` on `w`-bit basis indices, through the little-endian bit
view `basisBits w` (addition in `Fin w → ZMod 2`). -/
def xorConstPerm {w : ℕ} (c : Fin (2 ^ w)) : Equiv.Perm (Fin (2 ^ w)) :=
  (basisBits w).trans ((Equiv.addRight (basisBits w c)).trans (basisBits w).symm)

/-- Basis permutation on `Fin (2 ^ (m + w))` for the table lookup
`|x⟩|b⟩ ↦ |x⟩|b ⊕ f(x)⟩` (address `x` on the high `m` wires, target `b` on the low `w` wires).
It is an involution. -/
def tableXorPerm {m w : ℕ} (f : Fin (2 ^ m) → Fin (2 ^ w)) :
    Equiv.Perm (Fin (2 ^ (m + w))) :=
  (splitBasisEquiv m w).trans
    ((Equiv.prodShear (Equiv.refl _) fun x ↦ xorConstPerm (f x)).trans
      (splitBasisEquiv m w).symm)

/-- Lookup inputs: any address `x < L` and any target value. -/
def lookupValidInputs (p : LookupParams) : Set (Fin (2 ^ (p.m + p.w))) :=
  {i | ((splitBasisEquiv p.m p.w) i).1.val < p.L}

/-- Unlookup inputs: any address `x < L` whose target holds exactly `data(x)`. -/
def unlookupValidInputs {p : LookupParams} (data : LookupTable p) :
    Set (Fin (2 ^ (p.m + p.w))) :=
  {i | ((splitBasisEquiv p.m p.w) i).1.val < p.L ∧
    ((splitBasisEquiv p.m p.w) i).2 = data.extend ((splitBasisEquiv p.m p.w) i).1}

/-!
## Classical Variables

Measurement outcomes may be stored in any number of variables `v i`. The store holds
measurement results only; it has no assignment and no loops.
-/

/-- Classical variables for measurement outcomes. -/
inductive TableLookup.Var where | v (i : ℕ) deriving DecidableEq, Inhabited

open TableLookup (Var)

/-!
## Lookup: Holes and Frozen Theorems
-/

/-- Number of clean ancilla qubits `qromLookupProgram` uses for sizes `p`. -/
def qromLookupAncillas (p : LookupParams) : ℕ := sorry

/-- Lookup circuit for table `data` on the `p.m + p.w` data wires `rData` (`p.w` target wires
followed by `p.m` address wires) and `qromLookupAncillas p` clean ancilla wires `rAnc`. -/
def qromLookupProgram {n : ℕ} (p : LookupParams) (data : LookupTable p)
    (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromLookupAncillas p) n) : DynamicCircuit Var n :=
  sorry

/-- For valid sizes and every table, `qromLookupProgram` realizes `|x⟩|b⟩ ↦ |x⟩|b ⊕ data(x)⟩`
on every address `x < L` and every target `b`, as an exact clean subroutine across all disjoint
register placements. -/
theorem qromLookup_correctness (p : LookupParams) (hp : p.Valid) (data : LookupTable p)
    {n : ℕ} (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromLookupAncillas p) n) (hdisj : rData.DisjointWires rAnc) :
    RealizesCleanSubroutineOnEncoding rData rAnc hdisj (lookupValidInputs p)
      (tableXorPerm data.extend) (qromLookupProgram p data rData rAnc).compile := by
  sorry

/-- Claimed `T` count of the lookup, as a function of the sizes. -/
def qromLookupTCost (p : LookupParams) : ℕ := sorry

/-- For valid sizes, every table and every placement, the lookup uses no `TOFF` gates and at
most `qromLookupTCost p` `T` gates. -/
theorem qromLookup_t_cost (p : LookupParams) (hp : p.Valid) (data : LookupTable p)
    {n : ℕ} (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromLookupAncillas p) n) :
    (qromLookupProgram p data rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (qromLookupProgram p data rData rAnc).count PrimitiveGate.T ≤ qromLookupTCost p := by
  sorry

/-- Claimed spacetime cost `T count * (m + w + ancillas)` of the lookup, as a function of the
sizes. -/
def qromLookupSpacetimeCost (p : LookupParams) : ℕ := sorry

/-- For valid sizes, every table and every placement, the lookup uses no `TOFF` gates and has
`T count * (p.m + p.w + qromLookupAncillas p) ≤ qromLookupSpacetimeCost p`. -/
theorem qromLookup_spacetime_cost (p : LookupParams) (hp : p.Valid) (data : LookupTable p)
    {n : ℕ} (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromLookupAncillas p) n) :
    (qromLookupProgram p data rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (qromLookupProgram p data rData rAnc).count PrimitiveGate.T *
          (p.m + p.w + qromLookupAncillas p) ≤ qromLookupSpacetimeCost p := by
  sorry

/-- Pinned size for single-number records: `L = 1024` entries of `w = 32` bits, `m = 10`. -/
abbrev LookupParams.l1024w32 : LookupParams where
  L := 1024
  m := 10
  w := 32

/-- Claimed spacetime cost bound for the lookup at `LookupParams.l1024w32`. -/
def qromLookupL1024W32ConstCost : ℕ := sorry

/-- At `LookupParams.l1024w32`, for every table and every placement, the lookup uses no `TOFF`
gates and has `T count * (m + w + qromLookupAncillas) ≤ qromLookupL1024W32ConstCost`. -/
theorem qromLookup_l1024w32_const_cost (data : LookupTable .l1024w32) {n : ℕ}
    (rData : QRegister (LookupParams.l1024w32.m + LookupParams.l1024w32.w) n)
    (rAnc : QRegister (qromLookupAncillas .l1024w32) n) :
    (qromLookupProgram .l1024w32 data rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (qromLookupProgram .l1024w32 data rData rAnc).count PrimitiveGate.T *
          (LookupParams.l1024w32.m + LookupParams.l1024w32.w + qromLookupAncillas .l1024w32) ≤
        qromLookupL1024W32ConstCost := by
  sorry

/-!
## Unlookup: Holes and Frozen Theorems
-/

/-- Number of clean ancilla qubits `qromUnlookupProgram` uses for sizes `p`. -/
def qromUnlookupAncillas (p : LookupParams) : ℕ := sorry

/-- Unlookup circuit for table `data` on the `p.m + p.w` data wires `rData` (`p.w` target wires
followed by `p.m` address wires) and `qromUnlookupAncillas p` clean ancilla wires `rAnc`. -/
def qromUnlookupProgram {n : ℕ} (p : LookupParams) (data : LookupTable p)
    (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromUnlookupAncillas p) n) : DynamicCircuit Var n :=
  sorry

/-- For valid sizes and every table, `qromUnlookupProgram` realizes
`|x⟩|data(x)⟩ ↦ |x⟩|0⟩` on every address `x < L`, as an exact clean subroutine across all
disjoint register placements. Inputs whose target differs from `data(x)` are unconstrained. -/
theorem qromUnlookup_correctness (p : LookupParams) (hp : p.Valid) (data : LookupTable p)
    {n : ℕ} (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromUnlookupAncillas p) n) (hdisj : rData.DisjointWires rAnc) :
    RealizesCleanSubroutineOnEncoding rData rAnc hdisj (unlookupValidInputs data)
      (tableXorPerm data.extend) (qromUnlookupProgram p data rData rAnc).compile := by
  sorry

/-- Claimed `T` count of the unlookup, as a function of the sizes. -/
def qromUnlookupTCost (p : LookupParams) : ℕ := sorry

/-- For valid sizes, every table and every placement, the unlookup uses no `TOFF` gates and at
most `qromUnlookupTCost p` `T` gates. Classically controlled branches count as the larger
branch, so this bounds every measurement record. -/
theorem qromUnlookup_t_cost (p : LookupParams) (hp : p.Valid) (data : LookupTable p)
    {n : ℕ} (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromUnlookupAncillas p) n) :
    (qromUnlookupProgram p data rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (qromUnlookupProgram p data rData rAnc).count PrimitiveGate.T ≤ qromUnlookupTCost p := by
  sorry

/-- Claimed spacetime cost `T count * (m + w + ancillas)` of the unlookup, as a function of the
sizes. -/
def qromUnlookupSpacetimeCost (p : LookupParams) : ℕ := sorry

/-- For valid sizes, every table and every placement, the unlookup uses no `TOFF` gates and has
`T count * (p.m + p.w + qromUnlookupAncillas p) ≤ qromUnlookupSpacetimeCost p`. -/
theorem qromUnlookup_spacetime_cost (p : LookupParams) (hp : p.Valid) (data : LookupTable p)
    {n : ℕ} (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromUnlookupAncillas p) n) :
    (qromUnlookupProgram p data rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (qromUnlookupProgram p data rData rAnc).count PrimitiveGate.T *
          (p.m + p.w + qromUnlookupAncillas p) ≤ qromUnlookupSpacetimeCost p := by
  sorry

/-- Claimed spacetime cost bound for the unlookup at `LookupParams.l1024w32`. -/
def qromUnlookupL1024W32ConstCost : ℕ := sorry

/-- At `LookupParams.l1024w32`, for every table and every placement, the unlookup uses no `TOFF`
gates and has `T count * (m + w + qromUnlookupAncillas) ≤ qromUnlookupL1024W32ConstCost`. -/
theorem qromUnlookup_l1024w32_const_cost (data : LookupTable .l1024w32) {n : ℕ}
    (rData : QRegister (LookupParams.l1024w32.m + LookupParams.l1024w32.w) n)
    (rAnc : QRegister (qromUnlookupAncillas .l1024w32) n) :
    (qromUnlookupProgram .l1024w32 data rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (qromUnlookupProgram .l1024w32 data rData rAnc).count PrimitiveGate.T *
          (LookupParams.l1024w32.m + LookupParams.l1024w32.w + qromUnlookupAncillas .l1024w32) ≤
        qromUnlookupL1024W32ConstCost := by
  sorry

/-!
## Lookup and Unlookup with a Clean-Ancilla Budget

Published lookup records trade `T` gates for clean ancillas: select-swap lookup (Low,
Kliuchnikov and Schaeffer, arXiv:1812.00954; Berry et al., arXiv:1902.02134, Appendix A) loads
`k` words at a time into `k w` extra qubits and uses roughly `L / k + k w` Toffolis instead of
`L - 1`. That trade-off is a curve, not one number: it loses to unary iteration on
`T count * qubits`, so the spacetime theorems above cannot express it. The specs below take the
ancilla budget `a` as a size parameter. The ancilla count may be anything up to `a`, and the
claimed `T` count is a function of `(L, m, w, a)`, so a record is a point on the curve.
Correctness is the same as for the unbudgeted specs.
-/

/-- Sizes of a table lookup together with a clean-ancilla budget `a`. -/
structure BudgetLookupParams extends LookupParams where
  /-- Clean-ancilla budget `a`. -/
  a : ℕ

/-- The sizes are valid and the budget is at least `m`, which unary iteration needs. -/
def BudgetLookupParams.Valid (p : BudgetLookupParams) : Prop :=
  p.toLookupParams.Valid ∧ p.m ≤ p.a

/-- Pinned size and budget for single-number records: `L = 1024` entries of `w = 32` bits,
`m = 10`, and at most `a = 256` clean ancillas (room for `k = 4` words plus address workspace,
or `k = 8` words packed tightly). -/
abbrev BudgetLookupParams.l1024w32a256 : BudgetLookupParams where
  L := 1024
  m := 10
  w := 32
  a := 256

/-- Number of clean ancilla qubits `qromBudgetLookupProgram` uses. -/
def qromBudgetLookupAncillas (p : BudgetLookupParams) : ℕ := sorry

/-- Budgeted lookup circuit for table `data` on the `p.m + p.w` data wires `rData` (`p.w`
target wires followed by `p.m` address wires) and `qromBudgetLookupAncillas p` clean ancilla
wires `rAnc`. -/
def qromBudgetLookupProgram {n : ℕ} (p : BudgetLookupParams) (data : LookupTable p.toLookupParams)
    (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromBudgetLookupAncillas p) n) : DynamicCircuit Var n :=
  sorry

/-- For valid sizes and budget and every table, `qromBudgetLookupProgram` realizes
`|x⟩|b⟩ ↦ |x⟩|b ⊕ data(x)⟩` on every address `x < L` and every target `b`, as an exact clean
subroutine across all disjoint register placements. -/
theorem qromBudgetLookup_correctness (p : BudgetLookupParams) (hp : p.Valid)
    (data : LookupTable p.toLookupParams) {n : ℕ} (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromBudgetLookupAncillas p) n) (hdisj : rData.DisjointWires rAnc) :
    RealizesCleanSubroutineOnEncoding rData rAnc hdisj (lookupValidInputs p.toLookupParams)
      (tableXorPerm data.extend) (qromBudgetLookupProgram p data rData rAnc).compile := by
  sorry

/-- Claimed `T` count of the budgeted lookup, as a function of the sizes and the budget. -/
def qromBudgetLookupTCost (p : BudgetLookupParams) : ℕ := sorry

/-- For valid sizes and budget, every table and every placement, the budgeted lookup uses at
most `p.a` clean ancillas, no `TOFF` gates and at most `qromBudgetLookupTCost p` `T` gates. -/
theorem qromBudgetLookup_t_cost (p : BudgetLookupParams) (hp : p.Valid)
    (data : LookupTable p.toLookupParams) {n : ℕ} (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromBudgetLookupAncillas p) n) :
    qromBudgetLookupAncillas p ≤ p.a ∧
      (qromBudgetLookupProgram p data rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (qromBudgetLookupProgram p data rData rAnc).count PrimitiveGate.T ≤
        qromBudgetLookupTCost p := by
  sorry

/-- Claimed bound on `T count * (m + w + a)` for the budgeted lookup at
`BudgetLookupParams.l1024w32a256`. -/
def qromBudgetLookupL1024W32A256ConstCost : ℕ := sorry

/-- At `BudgetLookupParams.l1024w32a256`, for every table and every placement, the budgeted
lookup uses at most `256` clean ancillas, no `TOFF` gates and has
`T count * (m + w + a) ≤ qromBudgetLookupL1024W32A256ConstCost`, where `m + w + a = 298` is the
declared width. -/
theorem qromBudgetLookup_l1024w32a256_const_cost
    (data : LookupTable BudgetLookupParams.l1024w32a256.toLookupParams) {n : ℕ}
    (rData : QRegister (BudgetLookupParams.l1024w32a256.m + BudgetLookupParams.l1024w32a256.w) n)
    (rAnc : QRegister (qromBudgetLookupAncillas .l1024w32a256) n) :
    qromBudgetLookupAncillas .l1024w32a256 ≤ BudgetLookupParams.l1024w32a256.a ∧
      (qromBudgetLookupProgram .l1024w32a256 data rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (qromBudgetLookupProgram .l1024w32a256 data rData rAnc).count PrimitiveGate.T *
          (BudgetLookupParams.l1024w32a256.m + BudgetLookupParams.l1024w32a256.w +
            BudgetLookupParams.l1024w32a256.a) ≤
        qromBudgetLookupL1024W32A256ConstCost := by
  sorry

/-- Number of clean ancilla qubits `qromBudgetUnlookupProgram` uses. -/
def qromBudgetUnlookupAncillas (p : BudgetLookupParams) : ℕ := sorry

/-- Budgeted unlookup circuit for table `data` on the `p.m + p.w` data wires `rData` and
`qromBudgetUnlookupAncillas p` clean ancilla wires `rAnc`. -/
def qromBudgetUnlookupProgram {n : ℕ} (p : BudgetLookupParams)
    (data : LookupTable p.toLookupParams) (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromBudgetUnlookupAncillas p) n) : DynamicCircuit Var n :=
  sorry

/-- For valid sizes and budget and every table, `qromBudgetUnlookupProgram` realizes
`|x⟩|data(x)⟩ ↦ |x⟩|0⟩` on every address `x < L`, as an exact clean subroutine across all
disjoint register placements. Inputs whose target differs from `data(x)` are unconstrained. -/
theorem qromBudgetUnlookup_correctness (p : BudgetLookupParams) (hp : p.Valid)
    (data : LookupTable p.toLookupParams) {n : ℕ} (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromBudgetUnlookupAncillas p) n) (hdisj : rData.DisjointWires rAnc) :
    RealizesCleanSubroutineOnEncoding rData rAnc hdisj (unlookupValidInputs data)
      (tableXorPerm data.extend) (qromBudgetUnlookupProgram p data rData rAnc).compile := by
  sorry

/-- Claimed `T` count of the budgeted unlookup, as a function of the sizes and the budget. -/
def qromBudgetUnlookupTCost (p : BudgetLookupParams) : ℕ := sorry

/-- For valid sizes and budget, every table and every placement, the budgeted unlookup uses at
most `p.a` clean ancillas, no `TOFF` gates and at most `qromBudgetUnlookupTCost p` `T` gates.
Classically controlled branches count as the larger branch. -/
theorem qromBudgetUnlookup_t_cost (p : BudgetLookupParams) (hp : p.Valid)
    (data : LookupTable p.toLookupParams) {n : ℕ} (rData : QRegister (p.m + p.w) n)
    (rAnc : QRegister (qromBudgetUnlookupAncillas p) n) :
    qromBudgetUnlookupAncillas p ≤ p.a ∧
      (qromBudgetUnlookupProgram p data rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (qromBudgetUnlookupProgram p data rData rAnc).count PrimitiveGate.T ≤
        qromBudgetUnlookupTCost p := by
  sorry

/-- Claimed bound on `T count * (m + w + a)` for the budgeted unlookup at
`BudgetLookupParams.l1024w32a256`. -/
def qromBudgetUnlookupL1024W32A256ConstCost : ℕ := sorry

/-- At `BudgetLookupParams.l1024w32a256`, for every table and every placement, the budgeted
unlookup uses at most `256` clean ancillas, no `TOFF` gates and has
`T count * (m + w + a) ≤ qromBudgetUnlookupL1024W32A256ConstCost`. -/
theorem qromBudgetUnlookup_l1024w32a256_const_cost
    (data : LookupTable BudgetLookupParams.l1024w32a256.toLookupParams) {n : ℕ}
    (rData : QRegister (BudgetLookupParams.l1024w32a256.m + BudgetLookupParams.l1024w32a256.w) n)
    (rAnc : QRegister (qromBudgetUnlookupAncillas .l1024w32a256) n) :
    qromBudgetUnlookupAncillas .l1024w32a256 ≤ BudgetLookupParams.l1024w32a256.a ∧
      (qromBudgetUnlookupProgram .l1024w32a256 data rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      (qromBudgetUnlookupProgram .l1024w32a256 data rData rAnc).count PrimitiveGate.T *
          (BudgetLookupParams.l1024w32a256.m + BudgetLookupParams.l1024w32a256.w +
            BudgetLookupParams.l1024w32a256.a) ≤
        qromBudgetUnlookupL1024W32A256ConstCost := by
  sorry

end QuantumComputation.Specs
