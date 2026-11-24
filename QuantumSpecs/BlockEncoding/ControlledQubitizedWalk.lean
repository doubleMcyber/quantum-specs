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
public import QuantumComputationSpecs.Primitives.THCFactorization

/-!
# Controlled Qubitized Walk Operator of a Pauli Linear Combination of Unitaries

This is the controlled version of the qubitized walk specification (`QubitizedWalk.lean`), which
stays as it is. Given `N` system qubits, a number of terms `L ≥ 1`, a classical table that assigns
to every term `j < L` and every system qubit `q < N` one of the Paulis `I`, `X`, `Y`, `Z`, and
rational coefficients `c_0, …, c_{L-1}` of either sign, let `P_j` be the tensor product of row `j`
(no sign, no phase), `H = ∑_j c_j P_j`, and `λ = ∑_j |c_j|`, assumed positive. Given a precision
`μ` (a number of bits), the program acts on the system, an auxiliary register
(`cwalkAux N L μ` qubits; it plays the role of index, garbage and any sign qubit) and one control
qubit. It must realize one unitary: the identity when the control is `0`, and the qubitized walk
operator `W = (2 |0⟩⟨0|_aux ⊗ 1_sys - 1) · U` on system plus auxiliary when the control is `1`.
That is `|0⟩⟨0|_ctl ⊗ 1 + |1⟩⟨1|_ctl ⊗ W`. Here `U` is a self-inverse unitary on system plus
auxiliary whose block `(⟨0|_aux ⊗ 1) U (|0⟩_aux ⊗ 1)` equals `H' / λ` for a Hermitian `H'` with
spectral-norm distance `‖H' - H‖ ≤ λ / 2^μ`. The normalization is `λ`; the solver may not choose
it.

Why a separate specification: the uncontrolled walk specification cannot see a global phase, and
the walk operators of `H` and `-H` differ by the factor `-1`, so it does not distinguish `H` from
`-H`. In the controlled operation that factor is a phase of the control `1` branch relative to the
control `0` branch, which is observable, and phase estimation reads exactly that relative phase.
`cwalkOperator_neg_control_zero` and `cwalkOperator_neg_control_one` below state the point: `U` and
`-U` give the same action on control `0` and opposite action on control `1`. The global phase of
the whole controlled operation is still not observable and is not constrained.

Formally (`cwalk_correctness`): there exist a unitary `U` and an operator `H'` with
`IsQubitizedBlockEncodingUnitary λ H' U` (the definition of Google's THC specification, imported
from `QuantumComputationSpecs.Primitives.THCFactorization`: `0 < λ`, `Uᴴ = U` and
`P U P = λ⁻¹ • (P (H' ⊗ 1) P)` with `P` the projector onto `|0⟩` of the auxiliary register),
`H'` Hermitian and `‖H' - H‖ ≤ λ / 2^μ`, and the program realizes `cwalkOperator U` on every input
of system, auxiliary and control when the clean ancillas (`cwalkAncillas N L μ` qubits) start in
`|0⟩`, returning them to `|0⟩` (`RealizesCleanSubroutine`), for every disjoint register placement.
The table and coefficients are classical data known when the circuit is built, so the program may
depend on them arbitrarily. The statement holds for all `N`, `L`, `μ`, every table and every
coefficient vector with `λ > 0`.

Purpose (not part of the frozen statement): the controlled walk operator is the operation that
phase estimation applies. On the two-dimensional subspace of an eigenvector `|k⟩` of `H'` with
eigenvalue `E_k`, the walk operator has eigenphases `± arccos(E_k / λ)` (Low and Chuang; Babbush et
al., subsection "Encoding Spectra in Szegedy Quantum Walks using Qubitization Oracles"), and the
control makes them relative phases. This is a known theorem; the specification does not state or
require it.

Operator order: the reflection is applied after `U`, as in the uncontrolled specification and in
Babbush et al.'s walk operator `W = R_L · SELECT` up to conjugation by `PREPARE`.

Encoding (THC's layout with the control appended, and the library's little-endian convention,
`basisBits`): the program acts on a data register `rData` of `N + cwalkAux N L μ + 1` wires followed
by the ancilla register. Logical wires `0, …, N - 1` of `rData` are the system, wire `q` carrying
system qubit `q` (bit `q` of the system basis index `x`); logical wires `N, …, N + cwalkAux N L μ - 1`
are the auxiliary register; the last wire, `N + cwalkAux N L μ`, is the control. So the data basis
index is `x + 2^N * y + 2^(N + cwalkAux N L μ) * s` for system index `x`, auxiliary index `y` and
control bit `s`; the control is the most significant bit (`cwalkDataEquiv`). `P_j` applies `σ_{j,q}`
on system qubit `q`.

Cost: two theorems, both over Clifford + `T` with measurements, both excluding primitive `TOFF`
gates (so each Toffoli is costed by its Clifford + `T` construction, such as `4` `T` gates with an
ancilla and a measurement), and both holding for every table, every coefficient vector with
`λ > 0` and every register placement. `cwalk_t_cost` bounds the `T` count by the claimed
`cwalkTCost N L μ` for all `N`, `L ≥ 1` and `μ`, as in the THC specification.
`cwalk_n8l16mu8_spacetime_cost` bounds `T count * qubits` by the closed constant
`cwalkN8L16Mu8SpacetimeCost` at the pinned size `N = 8`, `L = 16`, `μ = 8`
(`CWalkSize.n8l16mu8`), as in Google's arcsine specification at `k25`, where
`qubits = N + cwalkAux N L μ + 1 + cwalkAncillas N L μ` counts all system, auxiliary, control and
clean ancilla qubits. The auxiliary width, the ancilla count and `cwalkTCost` depend only on
`(N, L, μ)`, never on the table or the coefficients.

Limits: the global phase of the whole controlled operation is free (a program realizing
`e^{iφ}` times the controlled walk passes), as in every specification of this library. Only the
phase of the control `1` branch relative to the control `0` branch is pinned. `H' = 0` is
admissible whenever `‖H‖ ≤ λ / 2^μ`, in particular for every input at `μ = 0`; the cost theorems
still hold for every `μ`. The program may be any circuit with the stated action; it need not be
built from `PREPARE` and `SELECT`.

References: G. H. Low and I. L. Chuang, "Hamiltonian Simulation by Qubitization", Quantum 3, 163
(2019), arXiv:1610.06546 (qubitization); R. Babbush, C. Gidney, D. W. Berry, N. Wiebe,
J. McClean, A. Paler, A. Fowler, H. Neven, "Encoding Electronic Spectra in Quantum Circuits with
Linear T Complexity", Phys. Rev. X 8, 041015 (2018), arXiv:1805.03662 (the walk operator
`R_L · SELECT` and its eigenphases `± arccos(E_k / λ)`); A. M. Childs and N. Wiebe,
arXiv:1202.5822 (linear combination of unitaries).
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator Matrix

/-!
## Pauli Strings and the Hamiltonian
-/

/-- A single-qubit Pauli operator. -/
inductive CWalk.Pauli where
  | I
  | X
  | Y
  | Z
  deriving DecidableEq, Inhabited

open CWalk (Pauli)

/-- The single-qubit unitary of a Pauli: `1`, and the library's `Qubit.X = !![0, 1; 1, 0]`,
`Qubit.Y = !![0, -i; i, 0]`, `Qubit.Z = !![1, 0; 0, -1]`. -/
noncomputable def CWalk.Pauli.unitary : Pauli → Unitary (2 ^ 1)
  | .I => 1
  | .X => Qubit.X
  | .Y => Qubit.Y
  | .Z => Qubit.Z

/-- Classical table of `L` Pauli strings on `N` qubits: row `j`, column `q` is the Pauli that
term `j` applies to system qubit `q`. -/
abbrev CWalkPauliTable (L N : ℕ) : Type := Fin L → Fin N → Pauli

/-- Classical table of `L` rational coefficients `c_0, …, c_{L-1}`, of either sign. -/
abbrev CWalkCoeffs (L : ℕ) : Type := Fin L → ℚ

/-- The Pauli string `⊗_q σ_q` of a row `σ : Fin N → Pauli`, with no sign or phase: the product
of `σ_q` placed on wire `q` of an `N`-qubit register, for `q = 0, …, N - 1`. The factors act on
distinct wires and commute, so the order of the product does not matter. -/
noncomputable def cwalkPauliString {N : ℕ} (row : Fin N → Pauli) : Unitary (2 ^ N) :=
  (List.ofFn fun q : Fin N ↦ (QRegister.singleton q).embedUnitary (row q).unitary).prod

/-- The `1`-norm `λ = ∑_j |c_j|` of a coefficient vector. -/
def cwalkLambda {L : ℕ} (c : CWalkCoeffs L) : ℚ :=
  ∑ j, |c j|

/-- The Hamiltonian `H = ∑_j c_j P_j` on `N` system qubits. -/
noncomputable def cwalkHamiltonian {L N : ℕ} (tbl : CWalkPauliTable L N) (c : CWalkCoeffs L) :
    Operator (2 ^ N) :=
  ∑ j, (c j : ℂ) • (cwalkPauliString (tbl j)).1

/-!
## The Walk Operator and its Controlled Version
-/

/-- Projector `|0⟩⟨0|_aux ⊗ 1_sys` onto the all-zero state of the auxiliary register (the last
`m` wires) of a system-plus-auxiliary register of `k + m` wires. It is the projector `P` of
`IsQubitizedBlockEncodingUnitary`. -/
noncomputable def cwalkAuxZeroProjector (k m : ℕ) : Operator (2 ^ (k + m)) :=
  (QRegister.block k m le_rfl : QRegister m (k + m)).basisOutcomeProjector 0

/-- The reflection `2 |0⟩⟨0|_aux ⊗ 1_sys - 1` about the all-zero state of the auxiliary
register. -/
noncomputable def cwalkReflection (k m : ℕ) : Unitary (2 ^ (k + m)) :=
  ⟨(2 : ℂ) • cwalkAuxZeroProjector k m - 1, by
    have hP2 : cwalkAuxZeroProjector k m * cwalkAuxZeroProjector k m =
        cwalkAuxZeroProjector k m :=
      QRegister.basisOutcomeProjector_mul_self _ _
    have hPh : (cwalkAuxZeroProjector k m)ᴴ = cwalkAuxZeroProjector k m :=
      QRegister.basisOutcomeProjector_conjTranspose _ _
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_smul, hPh, Matrix.conjTranspose_one]
    simp only [star_ofNat, sub_mul, mul_sub, smul_mul_smul_comm, hP2, mul_one, one_mul]
    module⟩

/-- The (uncontrolled) qubitized walk operator `(2 |0⟩⟨0|_aux ⊗ 1_sys - 1) · U` of a unitary `U`
on system (first `k` wires) plus auxiliary (last `m` wires). -/
noncomputable def cwalkWalkOperator {k m : ℕ} (U : Unitary (2 ^ (k + m))) :
    Unitary (2 ^ (k + m)) :=
  cwalkReflection k m * U

theorem cwalkWalkOperator_val {k m : ℕ} (U : Unitary (2 ^ (k + m))) :
    (cwalkWalkOperator U).1 = ((2 : ℂ) • cwalkAuxZeroProjector k m - 1) * U.1 := rfl

/-- Data basis index of control bit `s` and lower basis index `x` (system plus auxiliary):
`(s, x) ↦ x + 2^K * s` with `K = k + m` the number of lower wires, so the control is the most
significant bit, carried by the last data wire. -/
def cwalkDataEquiv (K : ℕ) : Fin 2 × Fin (2 ^ K) ≃ Fin (2 ^ (K + 1)) :=
  finProdFinEquiv.trans (finCongr (by rw [pow_succ, mul_comm]))

theorem cwalkDataEquiv_val (K : ℕ) (s : Fin 2) (x : Fin (2 ^ K)) :
    (cwalkDataEquiv K (s, x)).val = x.val + 2 ^ K * s.val := rfl

/-- Block-diagonal unitary `∑_s |s⟩⟨s| ⊗ B s`, reindexed to `Fin d` by `e`. -/
noncomputable def cwalkBlockDiagonal {m o : Type} [Fintype m] [DecidableEq m] [Fintype o]
    [DecidableEq o] {d : ℕ} (e : m × o ≃ Fin d) (B : o → 𝐔[m]) : Unitary d :=
  ⟨(blockDiagonal fun k ↦ (B k).1).submatrix e.symm e.symm, by
    have hB : ∀ k, (B k).1 * ((B k).1)ᴴ = 1 := fun k ↦ by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff.mp (B k).2
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
    simp only [hB]
    rw [← Pi.one_def, blockDiagonal_one, Matrix.submatrix_one_equiv]⟩

/-- The operation on system plus auxiliary selected by the control bit `s`: the identity for
`s = 0` and the walk operator of `U` for `s = 1`. -/
noncomputable def cwalkBlock {k m : ℕ} (U : Unitary (2 ^ (k + m))) (s : Fin 2) :
    Unitary (2 ^ (k + m)) :=
  if s = 0 then 1 else cwalkWalkOperator U

/-- The controlled qubitized walk operator on the `k + m + 1` data qubits (system, auxiliary,
control): `|0⟩⟨0|_ctl ⊗ 1 + |1⟩⟨1|_ctl ⊗ ((2 |0⟩⟨0|_aux ⊗ 1_sys - 1) · U)`, in the encoding
`cwalkDataEquiv` (control last, most significant). -/
noncomputable def cwalkOperator {k m : ℕ} (U : Unitary (2 ^ (k + m))) :
    Unitary (2 ^ (k + m + 1)) :=
  cwalkBlockDiagonal ((Equiv.prodComm _ _).trans (cwalkDataEquiv (k + m))) (cwalkBlock U)

/-!
## Sanity Checks
-/

/-- Column formula: `cwalkOperator U` keeps the control bit `s` and applies the block of `s` to the
lower wires, `|x⟩|s⟩ ↦ (∑_y (B_s)_{y x} |y⟩) ⊗ |s⟩`. -/
theorem cwalkOperator_mulVec_basisState {k m : ℕ} (U : Unitary (2 ^ (k + m))) (s : Fin 2)
    (x : Fin (2 ^ (k + m))) :
    (cwalkOperator U).1 *ᵥ basisState (cwalkDataEquiv (k + m) (s, x)) =
      ∑ y : Fin (2 ^ (k + m)), (cwalkBlock U s).1 y x •
        basisState (cwalkDataEquiv (k + m) (s, y)) := by
  ext d
  obtain ⟨⟨s', y'⟩, rfl⟩ := (cwalkDataEquiv (k + m)).surjective d
  simp only [basisState, Matrix.mulVec_single_one]
  by_cases hs : s' = s
  · subst hs
    simp [cwalkOperator, cwalkBlockDiagonal, Pi.single_apply, Finset.sum_apply]
  · simp [cwalkOperator, cwalkBlockDiagonal, hs, Finset.sum_apply, blockDiagonal_apply']

/-- Sanity check (a): `cwalkOperator U` fixes every basis state whose control bit is `0`: the
system and auxiliary bits are arbitrary and unchanged. -/
theorem cwalkOperator_control_zero {k m : ℕ} (U : Unitary (2 ^ (k + m)))
    (x : Fin (2 ^ (k + m))) :
    (cwalkOperator U).1 *ᵥ basisState (cwalkDataEquiv (k + m) (0, x)) =
      basisState (cwalkDataEquiv (k + m) (0, x)) := by
  rw [cwalkOperator_mulVec_basisState]
  simp [cwalkBlock, Matrix.one_apply]

/-- Sanity check (b): on a basis state with control bit `1`, `cwalkOperator U` acts as
`cwalkWalkOperator U` on the lower `k + m` wires and leaves the control at `1`,
`|x⟩|1⟩ ↦ (∑_y (W)_{y x} |y⟩) ⊗ |1⟩` with `W = (2 |0⟩⟨0|_aux ⊗ 1 - 1) · U`. -/
theorem cwalkOperator_control_one {k m : ℕ} (U : Unitary (2 ^ (k + m)))
    (x : Fin (2 ^ (k + m))) :
    (cwalkOperator U).1 *ᵥ basisState (cwalkDataEquiv (k + m) (1, x)) =
      ∑ y : Fin (2 ^ (k + m)), (cwalkWalkOperator U).1 y x •
        basisState (cwalkDataEquiv (k + m) (1, y)) := by
  rw [cwalkOperator_mulVec_basisState]
  simp [cwalkBlock]

/-- The walk operators of `U` and of a unitary `V` with `V = -U` (as matrices) differ by the sign:
`W(-U) = -W(U)`. This is the factor `-1` between the walk operators of `H` and `-H`. -/
theorem cwalkWalkOperator_neg {k m : ℕ} (U V : Unitary (2 ^ (k + m))) (hV : V.1 = -U.1) :
    (cwalkWalkOperator V).1 = -(cwalkWalkOperator U).1 := by
  rw [cwalkWalkOperator_val, cwalkWalkOperator_val, hV, mul_neg]

/-- Sanity check (c), control `0`: for a unitary `V` whose matrix is `-U`, `cwalkOperator V` and
`cwalkOperator U` agree on every basis state with control bit `0`. -/
theorem cwalkOperator_neg_control_zero {k m : ℕ} (U V : Unitary (2 ^ (k + m)))
    (_hV : V.1 = -U.1) (x : Fin (2 ^ (k + m))) :
    (cwalkOperator V).1 *ᵥ basisState (cwalkDataEquiv (k + m) (0, x)) =
      (cwalkOperator U).1 *ᵥ basisState (cwalkDataEquiv (k + m) (0, x)) := by
  rw [cwalkOperator_control_zero, cwalkOperator_control_zero]

/-- Sanity check (c), control `1`: for a unitary `V` whose matrix is `-U`, `cwalkOperator V` and
`cwalkOperator U` differ by the sign on every basis state with control bit `1`. So the controlled
walk distinguishes `U` from `-U` (and `H` from `-H`), which the uncontrolled walk does not. -/
theorem cwalkOperator_neg_control_one {k m : ℕ} (U V : Unitary (2 ^ (k + m)))
    (hV : V.1 = -U.1) (x : Fin (2 ^ (k + m))) :
    (cwalkOperator V).1 *ᵥ basisState (cwalkDataEquiv (k + m) (1, x)) =
      -((cwalkOperator U).1 *ᵥ basisState (cwalkDataEquiv (k + m) (1, x))) := by
  rw [cwalkOperator_control_one, cwalkOperator_control_one, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [cwalkWalkOperator_neg U V hV]
  simp

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive CWalk.Var where | v deriving DecidableEq, Inhabited

open CWalk (Var)
open CWalk.Var (v)

/-- Number of auxiliary qubits (index, garbage and any sign qubits) of the controlled walk
operator for `N` system qubits, `L` terms and precision `μ`, not counting the control qubit. The
reflection acts on all of them. It may not depend on the table or the coefficients. -/
def cwalkAux (N L μ : ℕ) : ℕ := sorry

/-- Number of clean ancilla qubits `cwalkProgram` uses for `N` system qubits, `L` terms and
precision `μ`. It may not depend on the table or the coefficients. -/
def cwalkAncillas (N L μ : ℕ) : ℕ := sorry

/-- Candidate controlled-walk circuit for the table `tbl` and coefficients `c` on
`N + cwalkAux N L μ + 1` data wires `rData` (`N` system wires, then the auxiliary wires, then the
control wire last) and `cwalkAncillas N L μ` clean ancilla wires `rAnc`. -/
def cwalkProgram {n : ℕ} (N L μ : ℕ) (tbl : CWalkPauliTable L N) (c : CWalkCoeffs L)
    (rData : QRegister (N + cwalkAux N L μ + 1) n)
    (rAnc : QRegister (cwalkAncillas N L μ) n) : DynamicCircuit Var n :=
  sorry

open scoped Matrix.Norms.L2Operator in
/-- For all `N`, `L ≥ 1`, `μ`, every table and every coefficient vector with `λ = ∑_j |c_j| > 0`,
there are a self-inverse unitary `U` on system plus auxiliary and a Hermitian `H'` with
`(⟨0|_aux ⊗ 1) U (|0⟩_aux ⊗ 1) = H' / λ` and `‖H' - H‖ ≤ λ / 2^μ` in spectral norm, such that
`cwalkProgram` acts as the controlled walk operator (the identity for control `0`,
`(2 |0⟩⟨0|_aux ⊗ 1 - 1) · U` on system plus auxiliary for control `1`) on every input of system,
auxiliary and control when the ancillas start in zero, returning the ancillas to zero, across all
disjoint register placements. -/
theorem cwalk_correctness (N L μ : ℕ) (hL : 1 ≤ L) (tbl : CWalkPauliTable L N)
    (c : CWalkCoeffs L) (hlam : 0 < cwalkLambda c) :
    ∃ (U : Unitary (2 ^ (N + cwalkAux N L μ))) (H' : Operator (2 ^ N)),
      IsQubitizedBlockEncodingUnitary ((cwalkLambda c : ℚ) : ℝ) H' U ∧
      H'.IsHermitian ∧
      ‖H' - cwalkHamiltonian tbl c‖ ≤ ((cwalkLambda c : ℚ) : ℝ) / 2 ^ μ ∧
      ∀ {n : ℕ}
        (rData : QRegister (N + cwalkAux N L μ + 1) n)
        (rAnc : QRegister (cwalkAncillas N L μ) n)
        (hdisj : rData.DisjointWires rAnc),
        RealizesCleanSubroutine rData rAnc hdisj (cwalkOperator U)
          (cwalkProgram N L μ tbl c rData rAnc).compile := by sorry

/-- `T`-gate count of `cwalkProgram`. -/
abbrev cwalkTCount {n : ℕ} (N L μ : ℕ) (tbl : CWalkPauliTable L N) (c : CWalkCoeffs L)
    (rData : QRegister (N + cwalkAux N L μ + 1) n)
    (rAnc : QRegister (cwalkAncillas N L μ) n) : ℕ :=
  (cwalkProgram N L μ tbl c rData rAnc).count PrimitiveGate.T

/-- Declared qubits: `N` system qubits, `cwalkAux N L μ` auxiliary qubits, one control qubit and
`cwalkAncillas N L μ` clean ancillas. -/
abbrev cwalkQubits (N L μ : ℕ) : ℕ :=
  N + cwalkAux N L μ + 1 + cwalkAncillas N L μ

/-!
## `T`-Count Cost Theorem

The cost theorem forbids primitive `TOFF` gates and bounds the `T` count by the claimed
`cwalkTCost N L μ`, for all sizes, every table, every coefficient vector with `λ > 0` and every
register placement.
-/

/-- Claimed `T` count of `cwalkProgram` for `N` system qubits, `L` terms and precision `μ`. It
depends only on `(N, L, μ)`. -/
def cwalkTCost (N L μ : ℕ) : ℕ := sorry

/-- For all `N`, `L ≥ 1`, `μ`, every table, every coefficient vector with `λ > 0` and every
register placement, `cwalkProgram` uses no `TOFF` gates and at most `cwalkTCost N L μ` `T`
gates. -/
theorem cwalk_t_cost (N L μ : ℕ) (hL : 1 ≤ L) (tbl : CWalkPauliTable L N)
    (c : CWalkCoeffs L) (hlam : 0 < cwalkLambda c) {n : ℕ}
    (rData : QRegister (N + cwalkAux N L μ + 1) n)
    (rAnc : QRegister (cwalkAncillas N L μ) n) :
    (cwalkProgram N L μ tbl c rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      cwalkTCount N L μ tbl c rData rAnc ≤ cwalkTCost N L μ := by sorry

/-!
## Spacetime Cost Theorem at the Pinned Size

The cost theorem forbids primitive `TOFF` gates and bounds `T count * qubits` by a closed `ℕ`
constant at `CWalkSize.n8l16mu8` (`N = 8` system qubits, `L = 16` terms, `μ = 8`), for every table,
every coefficient vector with `λ > 0` and every register placement.
-/

/-- Sizes of a controlled walk instance: `N` system qubits, `L` terms, precision `μ`. -/
structure CWalkSize where
  /-- Number of system qubits. -/
  N : ℕ
  /-- Number of terms. -/
  L : ℕ
  /-- Precision of the block encoding. -/
  μ : ℕ

/-- The pinned size `N = 8`, `L = 16`, `μ = 8`. -/
abbrev CWalkSize.n8l16mu8 : CWalkSize where
  N := 8
  L := 16
  μ := 8

/-- Claimed spacetime cost (`T count * qubits`) of `cwalkProgram` at `CWalkSize.n8l16mu8`. -/
def cwalkN8L16Mu8SpacetimeCost : ℕ := sorry

/-- At `CWalkSize.n8l16mu8`, for every table, every coefficient vector with `λ > 0` and every
register placement, `cwalkProgram` uses no `TOFF` gates and has
`T count * (N + auxiliary + 1 + ancillas)` at most `cwalkN8L16Mu8SpacetimeCost`. -/
theorem cwalk_n8l16mu8_spacetime_cost
    (tbl : CWalkPauliTable CWalkSize.n8l16mu8.L CWalkSize.n8l16mu8.N)
    (c : CWalkCoeffs CWalkSize.n8l16mu8.L) (hlam : 0 < cwalkLambda c) {n : ℕ}
    (rData : QRegister (CWalkSize.n8l16mu8.N +
      cwalkAux CWalkSize.n8l16mu8.N CWalkSize.n8l16mu8.L CWalkSize.n8l16mu8.μ + 1) n)
    (rAnc : QRegister (cwalkAncillas CWalkSize.n8l16mu8.N CWalkSize.n8l16mu8.L
      CWalkSize.n8l16mu8.μ) n) :
    (cwalkProgram CWalkSize.n8l16mu8.N CWalkSize.n8l16mu8.L CWalkSize.n8l16mu8.μ tbl c rData
        rAnc).count PrimitiveGate.TOFF = 0 ∧
      cwalkTCount CWalkSize.n8l16mu8.N CWalkSize.n8l16mu8.L CWalkSize.n8l16mu8.μ tbl c rData
          rAnc *
        cwalkQubits CWalkSize.n8l16mu8.N CWalkSize.n8l16mu8.L CWalkSize.n8l16mu8.μ ≤
      cwalkN8L16Mu8SpacetimeCost := by sorry

end QuantumComputation.Specs
