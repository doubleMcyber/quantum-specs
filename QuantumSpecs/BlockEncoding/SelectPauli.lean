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
public import QuantumComputation.Registers.Embed

/-!
# Pauli `SELECT` Specification

`SELECT` is the indexed operation of a linear combination of unitaries (Childs and Wiebe) whose
terms are signed Pauli strings. Given `b` index qubits, `N` system qubits, a number of terms `L`
with `1 ≤ L ≤ 2^b`, and a classical table that assigns to every term `j < L` a sign bit `s_j`
(`true` meaning `-1`) and, for every system qubit `q < N`, one of the Paulis `I`, `X`, `Y`, `Z`,
let `P_j` be the tensor product of row `j` (no phase) and `T_j = (-1)^(s_j) P_j`. The ideal
operation is `|ψ⟩|j⟩ ↦ (T_j |ψ⟩)|j⟩` for every `j < L` and every system state `|ψ⟩`. The relative
sign between different `j` is physical and is part of the ideal unitary.
For index values `j ≥ L` the solver chooses what is applied, but it must again be a signed Pauli
string that depends only on `j`: formally there must be a completion `tbl'` of the table to all
`2^b` index values (`SelectPauliCompletes`) such that the program realizes the `SELECT` unitary of
`tbl'` on every input of system plus index (`RealizesCleanSubroutine`). So the program is
block diagonal in the index and self-inverse on every input, which a qubitized walk built as
`PREPARE† · SELECT · PREPARE` needs, while unary iteration over `L < 2^b` terms keeps its freedom
at out-of-range index values. A global phase of the whole program is not observable and is not
constrained. A controlled `SELECT` is an instance of this specification: use `b + 1` index
qubits and a table of `2^b` rows `+I` followed by the `L` terms; the phase of each term is then
fixed against the identity.
Clean ancillas start in `|0⟩` and must be returned to `|0⟩`. The table is classical data known
when the circuit is built, so the program may depend on it arbitrarily. The correctness statement
holds for all `b`, `N`, `L` and all tables.

Encoding (the library's little-endian convention, `basisBits`; the same layout as the walk
specification, system first): the program acts on a data register `rData` of `N + b` wires
followed by the ancilla register. Logical wires `0, …, N - 1` of `rData` are the system, wire `q`
carrying bit `q` of the system basis index `x`; logical wires `N, …, N + b - 1` are the index
register, wire `N + i` carrying bit `i` of `j` (least significant first). So the data basis index
is `x + 2^N * j` (`selectPauliDataEquiv`), and `P_j` applies `σ_{j,q}` on system qubit `q`.
`selectPauli_pins_cnot` fixes this wire convention against the library's `CNOT` for `N = b = 1`,
`L = 2`, terms `+I` and `+X`.

Cost: two theorems, both over Clifford + `T` with measurements, both excluding primitive `TOFF`
gates (so each Toffoli is costed by its Clifford + `T` construction, such as `4` `T` gates with an
ancilla and a measurement), and both holding for every table and every register placement.
`selectPauli_t_cost` bounds the `T` count by the claimed `selectPauliTCost b N L` for all `b`,
`N`, `1 ≤ L ≤ 2^b`, as in the THC specification. `selectPauli_b4n8_spacetime_cost` bounds
`T count * qubits` by the closed constant `selectPauliB4N8SpacetimeCost` at the pinned size
`b = 4`, `N = 8`, `L = 16` (`SelectPauliSize.b4n8`), as in Google's arcsine specification at
`k25`, where `qubits = N + b + selectPauliAncillas b N L` counts all data and clean ancilla qubits.
`selectPauliAncillas` and `selectPauliTCost` depend only on `(b, N, L)`, never on the table.

References: R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler,
H. Neven, "Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity",
Phys. Rev. X 8, 041015 (2018), arXiv:1805.03662 (unary iteration; `T` count `4L - 4` for the
indexed operation); A. M. Childs and N. Wiebe, arXiv:1202.5822 (linear combination of
unitaries); G. H. Low and I. L. Chuang, arXiv:1610.06546 (qubitization).
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator Matrix

/-!
## Pauli Strings and the Ideal `SELECT` Unitary
-/

/-- A single-qubit Pauli operator. -/
inductive SelectPauli.Pauli where
  | I
  | X
  | Y
  | Z
  deriving DecidableEq, Inhabited

open SelectPauli (Pauli)

/-- The single-qubit unitary of a Pauli: `1`, and the library's `Qubit.X = !![0, 1; 1, 0]`,
`Qubit.Y = !![0, -i; i, 0]`, `Qubit.Z = !![1, 0; 0, -1]`. -/
noncomputable def SelectPauli.Pauli.unitary : Pauli → Unitary (2 ^ 1)
  | .I => 1
  | .X => Qubit.X
  | .Y => Qubit.Y
  | .Z => Qubit.Z

/-- Classical table of `L` signed Pauli strings on `N` qubits: entry `j` is a sign bit `s_j`
(`true` means the factor `-1`) together with a row, whose column `q` is the Pauli that term `j`
applies to system qubit `q`. -/
abbrev SelectPauliTable (L N : ℕ) : Type := Fin L → Bool × (Fin N → Pauli)

/-- The Pauli string `⊗_q σ_q` of a row `σ : Fin N → Pauli`, with no sign or phase: the product
of `σ_q` placed on wire `q` of an `N`-qubit register, for `q = 0, …, N - 1`. The factors act on
distinct wires and commute, so the order of the product does not matter. -/
noncomputable def selectPauliString {N : ℕ} (row : Fin N → Pauli) : Unitary (2 ^ N) :=
  (List.ofFn fun q : Fin N ↦ (QRegister.singleton q).embedUnitary (row q).unitary).prod

/-- The unitary `(-1)^s`, that is `-1` when `s = true` and `1` when `s = false`. -/
noncomputable def selectPauliSign (N : ℕ) (s : Bool) : Unitary (2 ^ N) :=
  if s then
    ⟨-1, by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      simp⟩
  else 1

/-- The signed Pauli string `(-1)^(s_j) P_j` of a table entry `(s_j, row)`. -/
noncomputable def selectPauliTerm {N : ℕ} (t : Bool × (Fin N → Pauli)) : Unitary (2 ^ N) :=
  selectPauliSign N t.1 * selectPauliString t.2

/-- Data basis index of index value `j` and system basis index `x`: `(j, x) ↦ x + 2^N * j`, so the
system occupies the `N` least significant bits (the first `N` data wires) and the index register
the next `b` bits. -/
def selectPauliDataEquiv (b N : ℕ) : Fin (2 ^ b) × Fin (2 ^ N) ≃ Fin (2 ^ (N + b)) :=
  finProdFinEquiv.trans (finCongr (by rw [pow_add, mul_comm]))

theorem selectPauliDataEquiv_val (b N : ℕ) (j : Fin (2 ^ b)) (x : Fin (2 ^ N)) :
    (selectPauliDataEquiv b N (j, x)).val = x.val + 2 ^ N * j.val := rfl

/-- Block-diagonal unitary `∑_k |k⟩⟨k| ⊗ B k`, reindexed to `Fin d` by `e`. -/
noncomputable def selectPauliBlockDiagonal {m o : Type} [Fintype m] [DecidableEq m] [Fintype o]
    [DecidableEq o] {d : ℕ} (e : m × o ≃ Fin d) (B : o → 𝐔[m]) : Unitary d :=
  ⟨(blockDiagonal fun k ↦ (B k).1).submatrix e.symm e.symm, by
    have hB : ∀ k, (B k).1 * ((B k).1)ᴴ = 1 := fun k ↦ by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff.mp (B k).2
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
    simp only [hB]
    rw [← Pi.one_def, blockDiagonal_one, Matrix.submatrix_one_equiv]⟩

/-- The system operation selected by index value `j`: the signed string `(-1)^(s_j) P_j` for
`j < L`, the identity otherwise. `selectPauli_correctness` uses it with `L = 2^b`, where every
index value has a row. -/
noncomputable def selectPauliBlock (b N L : ℕ) (tbl : SelectPauliTable L N) (j : Fin (2 ^ b)) :
    Unitary (2 ^ N) :=
  if h : j.val < L then selectPauliTerm (tbl ⟨j.val, h⟩) else 1

/-- Ideal `SELECT` unitary on the `N + b` data qubits:
`|x⟩|j⟩ ↦ (-1)^(s_j) (P_j |x⟩)|j⟩` for `j < L` (and `|x⟩|j⟩ ↦ |x⟩|j⟩` for `j ≥ L`), in the
encoding `selectPauliDataEquiv`. -/
noncomputable def selectPauliUnitary (b N L : ℕ) (tbl : SelectPauliTable L N) :
    Unitary (2 ^ (N + b)) :=
  selectPauliBlockDiagonal ((Equiv.prodComm _ _).trans (selectPauliDataEquiv b N))
    (selectPauliBlock b N L tbl)

/-- Sanity check: on a basis state with index `j < L`, `selectPauliUnitary` keeps the index and
applies the signed string to the system,
`|x⟩|j⟩ ↦ (∑_y ((-1)^(s_j) P_j)_{y x} |y⟩) ⊗ |j⟩`. -/
theorem selectPauliUnitary_mulVec_basisState (b N L : ℕ) (tbl : SelectPauliTable L N)
    (j : Fin (2 ^ b)) (hj : j.val < L) (x : Fin (2 ^ N)) :
    (selectPauliUnitary b N L tbl).1 *ᵥ basisState (selectPauliDataEquiv b N (j, x)) =
      ∑ y : Fin (2 ^ N), (selectPauliTerm (tbl ⟨j.val, hj⟩)).1 y x •
        basisState (selectPauliDataEquiv b N (j, y)) := by
  ext d
  obtain ⟨⟨j', y'⟩, rfl⟩ := (selectPauliDataEquiv b N).surjective d
  simp only [basisState, Matrix.mulVec_single_one]
  by_cases hj' : j' = j
  · subst hj'
    simp [selectPauliUnitary, selectPauliBlockDiagonal, selectPauliBlock, hj, Pi.single_apply,
      Finset.sum_apply]
  · simp [selectPauliUnitary, selectPauliBlockDiagonal, hj', Finset.sum_apply,
      blockDiagonal_apply']

/-- Sanity check: the one-qubit string `Y` maps `|0⟩` to `i |1⟩`. -/
theorem selectPauliString_Y_mulVec_zero :
    (selectPauliString (fun _ : Fin 1 ↦ Pauli.Y)).1 *ᵥ basisState 0 =
      Complex.I • basisState 1 := by
  simp only [selectPauliString, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    mul_one, QRegister.singleton_eq_whole, QRegister.whole_embedUnitary, SelectPauli.Pauli.unitary,
    basisState, Matrix.mulVec_single_one]
  ext i
  fin_cases i <;> simp [Qubit.Y]

/-- Sanity check: the one-qubit term with sign bit `true` and row `I` maps `|0⟩` to `-|0⟩`. -/
theorem selectPauliTerm_neg_I_mulVec_zero :
    (selectPauliTerm (true, fun _ : Fin 1 ↦ Pauli.I)).1 *ᵥ basisState 0 = -basisState 0 := by
  have h : (selectPauliTerm (true, fun _ : Fin 1 ↦ Pauli.I)).1 = -1 := by
    simp [selectPauliTerm, selectPauliSign, selectPauliString, List.ofFn_succ,
      QRegister.singleton_eq_whole, SelectPauli.Pauli.unitary]
  rw [h, Matrix.neg_mulVec, Matrix.one_mulVec]

/-- `tbl'` completes the table `tbl` to all `2^b` index values: it has the same row as `tbl` for
every `j < L`. Its rows for `j ≥ L` are not constrained. -/
def SelectPauliCompletes (b N L : ℕ) (tbl : SelectPauliTable L N)
    (tbl' : SelectPauliTable (2 ^ b) N) : Prop :=
  ∀ (j : Fin L) (h : j.val < 2 ^ b), tbl' ⟨j.val, h⟩ = tbl j

set_option maxRecDepth 20000 in
/-- Wire pinning: for `N = b = 1` and `L = 2` with term `0` equal to `+I` and term `1` equal to
`+X`, the ideal unitary is the library's `CNOT` with control on data wire `1` (the index) and
target on data wire `0` (the system), where `CNOT` has the library's gate semantics
(`PrimitiveGate.cnotUnitary`, via `Circuit.eval`). This fixes the wire order, the bit order and
the sign convention of the whole statement. -/
theorem selectPauli_pins_cnot (tbl : SelectPauliTable 2 1)
    (h0 : tbl 0 = (false, fun _ ↦ Pauli.I)) (h1 : tbl 1 = (false, fun _ ↦ Pauli.X)) :
    selectPauliUnitary 1 1 2 tbl = (Circuit.CNOT (1 : Fin 2) 0 (by decide)).eval := by
  have hemp : IsEmpty (QRegister.pair (1 : Fin 2) 0 (by decide)).Environment :=
    ⟨fun ⟨q, hq⟩ ↦ by
      fin_cases q
      · exact hq ⟨1, rfl⟩
      · exact hq ⟨0, rfl⟩⟩
  have hext : ∀ i : Fin 4, (QRegister.pair (1 : Fin 2) 0 (by decide)).extractIndex i =
      ![0, 2, 1, 3] i := by
    decide
  have hentry : ∀ i k : Fin 4, (Circuit.CNOT (1 : Fin 2) 0 (by decide)).eval.1 i k =
      PrimitiveGate.cnotUnitary.1 (![0, 2, 1, 3] i) (![0, 2, 1, 3] k) := by
    intro i k
    change (QRegister.pair (1 : Fin 2) 0 (by decide)).embedMatrix PrimitiveGate.cnotUnitary.1 i k = _
    have hc : ((QRegister.pair (1 : Fin 2) 0 (by decide)).basisSplitEquiv i).2 =
        ((QRegister.pair (1 : Fin 2) 0 (by decide)).basisSplitEquiv k).2 := Subsingleton.elim _ _
    rw [QRegister.embedMatrix_apply, hext, hext]
    simp [hc]
  have hE : ∀ (j : Fin (2 ^ 1)) (x : Fin (2 ^ 1)), selectPauliDataEquiv 1 1 (j, x) =
      ⟨x.val + 2 * j.val, by have := j.2; have := x.2; omega⟩ := fun j x ↦
    Fin.ext (selectPauliDataEquiv_val 1 1 j x)
  have t1 : ∀ h : 1 < 2, tbl ⟨1, h⟩ = (false, fun _ ↦ Pauli.X) := fun _ ↦ h1
  have hL := selectPauliUnitary_mulVec_basisState 1 1 2 tbl
  apply Subtype.ext
  ext i k
  rw [hentry]
  obtain ⟨⟨j', y'⟩, rfl⟩ := (selectPauliDataEquiv 1 1).surjective i
  obtain ⟨⟨j, x⟩, rfl⟩ := (selectPauliDataEquiv 1 1).surjective k
  have hj : j.val < 2 := by simpa using j.isLt
  have hcol := congrFun (hL j hj x) (selectPauliDataEquiv 1 1 (j', y'))
  have hU : (selectPauliUnitary 1 1 2 tbl).1 (selectPauliDataEquiv 1 1 (j', y'))
      (selectPauliDataEquiv 1 1 (j, x)) =
      ∑ y : Fin (2 ^ 1), (selectPauliTerm (tbl ⟨j.val, hj⟩)).1 y x *
        basisState (selectPauliDataEquiv 1 1 (j, y)) (selectPauliDataEquiv 1 1 (j', y')) := by
    simpa [basisState, Matrix.mulVec_single_one, Finset.sum_apply] using hcol
  rw [hU]
  have hcn : ∀ a b : Fin 4, PrimitiveGate.cnotUnitary.1 a b =
      if Equiv.swap (1 : Fin 4) 3 a = b then 1 else 0 := by
    intro a b
    simp [PrimitiveGate.cnotUnitary, permutationUnitary, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Equiv.swap_inv]
  rw [hcn]
  have hs : ∀ f : Fin (2 ^ 1) → ℂ, ∑ y, f y = f 0 + f 1 := fun f ↦ Fin.sum_univ_two f
  fin_cases j <;> fin_cases x <;> fin_cases j' <;> fin_cases y'
  all_goals
    simp only [hs, Fin.zero_eta, Fin.isValue, Fin.val_zero, t1, hE]
  all_goals
    simp [h0, selectPauliTerm, selectPauliSign, selectPauliString, List.ofFn_succ,
      QRegister.singleton_eq_whole, QRegister.whole_embedUnitary, SelectPauli.Pauli.unitary,
      Qubit.X, basisState, Fin.ext_iff, Equiv.swap_apply_def]

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive SelectPauli.Var where | v deriving DecidableEq, Inhabited

open SelectPauli (Var)
open SelectPauli.Var (v)

/-- Number of clean ancilla qubits `selectPauliProgram` uses for `b` index qubits, `N` system
qubits and `L` terms. It may not depend on the table. -/
def selectPauliAncillas (b N L : ℕ) : ℕ := sorry

/-- Candidate `SELECT` circuit for the table `tbl` on `N + b` data wires `rData` (`N` system
wires followed by `b` index wires, least significant first) and `selectPauliAncillas b N L` clean
ancilla wires `rAnc`. -/
def selectPauliProgram {n : ℕ} (b N L : ℕ) (tbl : SelectPauliTable L N)
    (rData : QRegister (N + b) n)
    (rAnc : QRegister (selectPauliAncillas b N L) n) : DynamicCircuit Var n :=
  sorry

/-- For all `b`, `N`, `1 ≤ L ≤ 2^b` and every table, there is a completion `tbl'` of the table to
all `2^b` index values such that `selectPauliProgram` realizes
`|ψ⟩|j⟩|0⟩ ↦ (T'_j |ψ⟩)|j⟩|0⟩` on every input of system plus index whose ancillas are `|0⟩`,
across all disjoint register placements, where `T'_j = T_j = (-1)^(s_j) P_j` for `j < L` and
`T'_j` for `j ≥ L` is a signed Pauli string of the solver's choice. -/
theorem selectPauli_correctness (b N L : ℕ) (hL : 1 ≤ L) (hLb : L ≤ 2 ^ b)
    (tbl : SelectPauliTable L N) :
    ∃ tbl' : SelectPauliTable (2 ^ b) N,
      SelectPauliCompletes b N L tbl tbl' ∧
      ∀ {n : ℕ}
        (rData : QRegister (N + b) n)
        (rAnc : QRegister (selectPauliAncillas b N L) n)
        (hdisj : rData.DisjointWires rAnc),
        RealizesCleanSubroutine rData rAnc hdisj (selectPauliUnitary b N (2 ^ b) tbl')
          (selectPauliProgram b N L tbl rData rAnc).compile := by sorry

/-- `T`-gate count of `selectPauliProgram`. -/
abbrev selectPauliTCount {n : ℕ} (b N L : ℕ) (tbl : SelectPauliTable L N)
    (rData : QRegister (N + b) n)
    (rAnc : QRegister (selectPauliAncillas b N L) n) : ℕ :=
  (selectPauliProgram b N L tbl rData rAnc).count PrimitiveGate.T

/-- Declared qubits: `N + b` data qubits and `selectPauliAncillas b N L` clean ancillas. -/
abbrev selectPauliQubits (b N L : ℕ) : ℕ :=
  N + b + selectPauliAncillas b N L

/-!
## `T`-Count Cost Theorem

The cost theorem forbids primitive `TOFF` gates and bounds the `T` count by the claimed
`selectPauliTCost b N L`, for all sizes, every table and every register placement.
-/

/-- Claimed `T` count of `selectPauliProgram` for `b` index qubits, `N` system qubits and `L`
terms. It depends only on `(b, N, L)`. -/
def selectPauliTCost (b N L : ℕ) : ℕ := sorry

/-- For all `b`, `N`, `1 ≤ L ≤ 2^b`, every table and every register placement,
`selectPauliProgram` uses no `TOFF` gates and at most `selectPauliTCost b N L` `T` gates. -/
theorem selectPauli_t_cost (b N L : ℕ) (hL : 1 ≤ L) (hLb : L ≤ 2 ^ b)
    (tbl : SelectPauliTable L N) {n : ℕ}
    (rData : QRegister (N + b) n)
    (rAnc : QRegister (selectPauliAncillas b N L) n) :
    (selectPauliProgram b N L tbl rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      selectPauliTCount b N L tbl rData rAnc ≤ selectPauliTCost b N L := by sorry

/-!
## Spacetime Cost Theorem at the Pinned Size

The cost theorem forbids primitive `TOFF` gates and bounds `T count * qubits` by a closed `ℕ`
constant at `SelectPauliSize.b4n8` (`b = 4` index qubits, `N = 8` system qubits, `L = 16 = 2^b`
terms), for every table and every register placement.
-/

/-- Sizes of a `SELECT` instance: `b` index qubits, `N` system qubits, `L` terms. -/
structure SelectPauliSize where
  /-- Number of index qubits. -/
  b : ℕ
  /-- Number of system qubits. -/
  N : ℕ
  /-- Number of terms. -/
  L : ℕ

/-- The pinned size `b = 4`, `N = 8`, `L = 16`. -/
abbrev SelectPauliSize.b4n8 : SelectPauliSize where
  b := 4
  N := 8
  L := 16

/-- Claimed spacetime cost (`T count * qubits`) of `selectPauliProgram` at
`SelectPauliSize.b4n8`. -/
def selectPauliB4N8SpacetimeCost : ℕ := sorry

/-- At `SelectPauliSize.b4n8`, for every table and every register placement,
`selectPauliProgram` uses no `TOFF` gates and has `T count * (N + b + ancillas)` at most
`selectPauliB4N8SpacetimeCost`. -/
theorem selectPauli_b4n8_spacetime_cost
    (tbl : SelectPauliTable SelectPauliSize.b4n8.L SelectPauliSize.b4n8.N) {n : ℕ}
    (rData : QRegister (SelectPauliSize.b4n8.N + SelectPauliSize.b4n8.b) n)
    (rAnc : QRegister (selectPauliAncillas SelectPauliSize.b4n8.b SelectPauliSize.b4n8.N
      SelectPauliSize.b4n8.L) n) :
    (selectPauliProgram SelectPauliSize.b4n8.b SelectPauliSize.b4n8.N SelectPauliSize.b4n8.L
        tbl rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      selectPauliTCount SelectPauliSize.b4n8.b SelectPauliSize.b4n8.N SelectPauliSize.b4n8.L
          tbl rData rAnc *
        selectPauliQubits SelectPauliSize.b4n8.b SelectPauliSize.b4n8.N SelectPauliSize.b4n8.L ≤
      selectPauliB4N8SpacetimeCost := by sorry

end QuantumComputation.Specs
