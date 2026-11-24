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
# Qubitized Walk Operator of a Pauli Linear Combination of Unitaries

Given `N` system qubits, a number of terms `L ≥ 1`, a classical table that assigns to every term
`j < L` and every system qubit `q < N` one of the Paulis `I`, `X`, `Y`, `Z`, and rational
coefficients `c_0, …, c_{L-1}` of either sign, let `P_j` be the tensor product of row `j` (no
sign, no phase), `H = ∑_j c_j P_j`, and `λ = ∑_j |c_j|`, assumed positive. Given a precision `μ`
(a number of bits), the program must act on an auxiliary register (`walkAux N L μ` qubits; it
plays the role of index, garbage and any sign qubit) and the `N` system qubits as one unitary, the
qubitized walk operator
`W = (2 |0⟩⟨0|_aux ⊗ 1_sys - 1) · U`,
where `U` is a self-inverse unitary on auxiliary plus system whose block
`(⟨0|_aux ⊗ 1) U (|0⟩_aux ⊗ 1)` equals `H' / λ` for a Hermitian `H'` with spectral-norm distance
`‖H' - H‖ ≤ λ / 2^μ`. The normalization is `λ`; the solver may not choose it.
A global phase of the whole program is not observable and is not constrained. The walk operators
of `H` and `-H` differ by the factor `-1`, so this specification does not distinguish `H` from
`-H`. The controlled walk operator, which phase estimation uses, does; it is a separate
specification.

Formally (`walk_correctness`): there exist a unitary `U` and an operator `H'` with
`IsQubitizedBlockEncodingUnitary λ H' U` (the definition of Google's THC specification, imported
from `QuantumComputationSpecs.Primitives.THCFactorization`: `0 < λ`, `Uᴴ = U` and
`P U P = λ⁻¹ • (P (H' ⊗ 1) P)` with `P` the projector onto `|0⟩` of the auxiliary register),
`H'` Hermitian and `‖H' - H‖ ≤ λ / 2^μ`, and the program realizes `walkOperator U` on every input
of system plus auxiliary when the clean ancillas (`walkAncillas N L μ` qubits) start in `|0⟩`,
returning them to `|0⟩` (`RealizesCleanSubroutine`), for every disjoint register placement. The
table and coefficients are classical data known when the circuit is built, so the program may
depend on them arbitrarily. The statement holds for all `N`, `L`, `μ`, every table and every
coefficient vector with `λ > 0`.

Purpose (not part of the frozen statement): for self-inverse `U` with block `H' / λ`, the walk
operator acts on each two-dimensional subspace spanned by `|0⟩_aux |k⟩` and `W |0⟩_aux |k⟩`, for an
eigenvector `|k⟩` of `H'` with eigenvalue `E_k`, as a rotation with eigenphases
`± arccos(E_k / λ)`, which phase estimation reads out (Low and Chuang; Babbush et al.,
subsection "Encoding Spectra in Szegedy Quantum Walks using Qubitization Oracles"). This is a
known theorem; the specification does not state or require it.

Operator order: the reflection is applied after `U`, as in Babbush et al.'s walk operator
`W = R_L · SELECT` with `R_L = 2 |L⟩⟨L| ⊗ 1 - 1`. Conjugating by `PREPARE` (`|0⟩ ↦ |L⟩`) turns
that operator into `(2 |0⟩⟨0| ⊗ 1 - 1) · PREPARE† · SELECT · PREPARE`, which has this form with
`U = PREPARE† · SELECT · PREPARE`.

Encoding (THC's layout and the library's little-endian convention, `basisBits`): the program
acts on a data register `rData` of `N + walkAux N L μ` wires followed by the ancilla register.
Logical wires `0, …, N - 1` of `rData` are the system, wire `q` carrying system qubit `q` (bit `q`
of the system basis index `x`); logical wires `N, …` are the auxiliary register, so the data basis
index is `x + 2^N * y` for auxiliary basis index `y`. `P_j` applies `σ_{j,q}` on system qubit
`q`.
The layout is chosen so that the family composes: with the auxiliary register holding an index
register first and a garbage register after it, the `SELECT` specification applies to the system
and index wires and the `PREPARE` specification to the auxiliary wires.

Cost: two theorems, both over Clifford + `T` with measurements, both excluding primitive `TOFF`
gates (so each Toffoli is costed by its Clifford + `T` construction, such as `4` `T` gates with an
ancilla and a measurement), and both holding for every table, every coefficient vector with
`λ > 0` and every register placement. `walk_t_cost` bounds the `T` count by the claimed
`walkTCost N L μ` for all `N`, `L ≥ 1` and `μ`, as in the THC specification.
`walk_n8l16mu8_spacetime_cost` bounds `T count * qubits` by the closed constant
`walkN8L16Mu8SpacetimeCost` at the pinned size `N = 8`, `L = 16`, `μ = 8` (`WalkSize.n8l16mu8`),
as in Google's arcsine specification at `k25`, where
`qubits = N + walkAux N L μ + walkAncillas N L μ` counts all system, auxiliary and clean ancilla
qubits. The auxiliary width, the ancilla count and `walkTCost` depend only on `(N, L, μ)`, never
on the table or the coefficients.

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
inductive Walk.Pauli where
  | I
  | X
  | Y
  | Z
  deriving DecidableEq, Inhabited

open Walk (Pauli)

/-- The single-qubit unitary of a Pauli: `1`, and the library's `Qubit.X = !![0, 1; 1, 0]`,
`Qubit.Y = !![0, -i; i, 0]`, `Qubit.Z = !![1, 0; 0, -1]`. -/
noncomputable def Walk.Pauli.unitary : Pauli → Unitary (2 ^ 1)
  | .I => 1
  | .X => Qubit.X
  | .Y => Qubit.Y
  | .Z => Qubit.Z

/-- Classical table of `L` Pauli strings on `N` qubits: row `j`, column `q` is the Pauli that
term `j` applies to system qubit `q`. -/
abbrev WalkPauliTable (L N : ℕ) : Type := Fin L → Fin N → Pauli

/-- Classical table of `L` rational coefficients `c_0, …, c_{L-1}`, of either sign. -/
abbrev WalkCoeffs (L : ℕ) : Type := Fin L → ℚ

/-- The Pauli string `⊗_q σ_q` of a row `σ : Fin N → Pauli`, with no sign or phase: the product
of `σ_q` placed on wire `q` of an `N`-qubit register, for `q = 0, …, N - 1`. The factors act on
distinct wires and commute, so the order of the product does not matter. -/
noncomputable def walkPauliString {N : ℕ} (row : Fin N → Pauli) : Unitary (2 ^ N) :=
  (List.ofFn fun q : Fin N ↦ (QRegister.singleton q).embedUnitary (row q).unitary).prod

/-- The `1`-norm `λ = ∑_j |c_j|` of a coefficient vector. -/
def walkLambda {L : ℕ} (c : WalkCoeffs L) : ℚ :=
  ∑ j, |c j|

/-- The Hamiltonian `H = ∑_j c_j P_j` on `N` system qubits. -/
noncomputable def walkHamiltonian {L N : ℕ} (tbl : WalkPauliTable L N) (c : WalkCoeffs L) :
    Operator (2 ^ N) :=
  ∑ j, (c j : ℂ) • (walkPauliString (tbl j)).1

/-!
## The Walk Operator
-/

/-- Projector `|0⟩⟨0|_aux ⊗ 1_sys` onto the all-zero state of the auxiliary register (the last
`m` wires) of a system-plus-auxiliary register of `k + m` wires. It is the projector `P` of
`IsQubitizedBlockEncodingUnitary`. -/
noncomputable def walkAuxZeroProjector (k m : ℕ) : Operator (2 ^ (k + m)) :=
  (QRegister.block k m le_rfl : QRegister m (k + m)).basisOutcomeProjector 0

/-- The reflection `2 |0⟩⟨0|_aux ⊗ 1_sys - 1` about the all-zero state of the auxiliary
register. -/
noncomputable def walkReflection (k m : ℕ) : Unitary (2 ^ (k + m)) :=
  ⟨(2 : ℂ) • walkAuxZeroProjector k m - 1, by
    have hP2 : walkAuxZeroProjector k m * walkAuxZeroProjector k m = walkAuxZeroProjector k m :=
      QRegister.basisOutcomeProjector_mul_self _ _
    have hPh : (walkAuxZeroProjector k m)ᴴ = walkAuxZeroProjector k m :=
      QRegister.basisOutcomeProjector_conjTranspose _ _
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_smul, hPh, Matrix.conjTranspose_one]
    simp only [star_ofNat, sub_mul, mul_sub, smul_mul_smul_comm, hP2, mul_one, one_mul]
    module⟩

/-- The qubitized walk operator `(2 |0⟩⟨0|_aux ⊗ 1_sys - 1) · U` of a unitary `U` on system
(first `k` wires) plus auxiliary (last `m` wires). -/
noncomputable def walkOperator {k m : ℕ} (U : Unitary (2 ^ (k + m))) : Unitary (2 ^ (k + m)) :=
  walkReflection k m * U

theorem walkOperator_val {k m : ℕ} (U : Unitary (2 ^ (k + m))) :
    (walkOperator U).1 = ((2 : ℂ) • walkAuxZeroProjector k m - 1) * U.1 := rfl

/-!
## Sanity Checks
-/

/-- Each Pauli matrix is Hermitian. -/
theorem Walk.Pauli.unitary_isHermitian (σ : Pauli) : σ.unitary.1.IsHermitian := by
  unfold Matrix.IsHermitian
  cases σ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Walk.Pauli.unitary, Qubit.X, Qubit.Y, Qubit.Z]

/-- A product of pairwise commuting Hermitian matrices is Hermitian. -/
theorem walk_list_prod_isHermitian {d : ℕ} (l : List (Operator d))
    (hH : ∀ A ∈ l, A.IsHermitian) (hc : l.Pairwise Commute) : l.prod.IsHermitian := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hc
    have ha : a.IsHermitian := hH a (by simp)
    have hl : l.prod.IsHermitian := ih (fun A hA ↦ hH A (by simp [hA])) hc.2
    have hcomm : Commute a l.prod := Commute.list_prod_right _ _ hc.1
    rw [List.prod_cons]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, hl.eq, ha.eq]
    exact hcomm.eq.symm

/-- Every Pauli string is Hermitian. -/
theorem walkPauliString_isHermitian {N : ℕ} (row : Fin N → Pauli) :
    (walkPauliString row).1.IsHermitian := by
  unfold walkPauliString
  rw [Submonoid.coe_list_prod, List.map_ofFn]
  apply walk_list_prod_isHermitian
  · intro A hA
    obtain ⟨q, rfl⟩ := List.mem_ofFn.mp hA
    simp only [Function.comp_apply, QRegister.embedUnitary_val]
    unfold Matrix.IsHermitian
    rw [← QRegister.embedMatrix_conjTranspose, (row q).unitary_isHermitian.eq]
  · refine List.pairwise_ofFn.mpr fun i j hij ↦ ?_
    simp only [Function.comp_apply, QRegister.embedUnitary_val]
    exact QRegister.embedMatrix_comm_of_disjoint _ _ (QRegister.singleton_disjoint hij.ne) _ _

/-- The Hamiltonian `H = ∑_j c_j P_j` is Hermitian (the coefficients are real). -/
theorem walkHamiltonian_isHermitian {L N : ℕ} (tbl : WalkPauliTable L N) (c : WalkCoeffs L) :
    (walkHamiltonian tbl c).IsHermitian := by
  unfold Matrix.IsHermitian walkHamiltonian
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Matrix.conjTranspose_smul, (walkPauliString_isHermitian (tbl j)).eq]
  simp

/-- `λ` is the sum of absolute values: for `c = (1, -1)` it is `2`, not `0`. -/
theorem walkLambda_one_neg_one : walkLambda (![1, -1] : WalkCoeffs 2) = 2 := by
  norm_num [walkLambda, Fin.sum_univ_two]

/-- The projector onto the zero state of an empty register is the identity. -/
theorem walk_basisOutcomeProjector_width_zero {n : ℕ} (r : QRegister 0 n) :
    r.basisOutcomeProjector 0 = 1 := by
  ext i j
  have h : r.extractIndex i = 0 := Fin.ext (by
    have := (r.extractIndex i).isLt
    simp only [pow_zero] at this
    simp only [Fin.val_zero]
    omega)
  simp [QRegister.basisOutcomeProjector_apply, Matrix.one_apply, h]

/-- With an empty auxiliary register the walk operator of `U` is `U`: the reflection is the
identity. -/
theorem walkOperator_aux_zero {k : ℕ} (U : Unitary (2 ^ (k + 0))) : walkOperator U = U := by
  apply Subtype.ext
  rw [walkOperator_val, walkAuxZeroProjector, walk_basisOutcomeProjector_width_zero, two_smul,
    add_sub_cancel_right, one_mul]

/-- The block `0, …, k - 1` of a `k + 0`-wire register is the whole register. -/
theorem walk_block_zero_eq_whole (k : ℕ) (h : 0 + k ≤ k + 0) :
    (QRegister.block 0 k h : QRegister k (k + 0)) = QRegister.whole k := by
  ext i
  simp

/-- Embedding into the block `0, …, k - 1` of a `k + 0`-wire register changes nothing. -/
theorem walk_block_zero_embedMatrix (k : ℕ) (h : 0 + k ≤ k + 0) (A : Operator (2 ^ k)) :
    (QRegister.block 0 k h : QRegister k (k + 0)).embedMatrix A = A := by
  rw [walk_block_zero_eq_whole]
  exact QRegister.whole_embedMatrix A

open scoped Matrix.Norms.L2Operator in
/-- Sanity check of the target: for one term with coefficient `1` and no auxiliary qubits, the
Pauli string itself is a qubitized block-encoding of `H = P_0` with normalization `λ = 1`, `H` is
Hermitian, its distance to `H` is `0 ≤ λ / 2^μ`, and the walk operator is the Pauli string. So
the existential part of `walk_correctness` is satisfiable, and with the reflection sign reversed
(`1 - 2 |0⟩⟨0|`) the last conjunct would fail. -/
theorem walk_target_one_term (N μ : ℕ) (row : Fin N → Pauli) :
    let tbl : WalkPauliTable 1 N := fun _ ↦ row
    let c : WalkCoeffs 1 := ![1]
    ∃ (U : Unitary (2 ^ (N + 0))) (H' : Operator (2 ^ N)),
      IsQubitizedBlockEncodingUnitary ((walkLambda c : ℚ) : ℝ) H' U ∧
      H'.IsHermitian ∧
      ‖H' - walkHamiltonian tbl c‖ ≤ ((walkLambda c : ℚ) : ℝ) / 2 ^ μ ∧
      walkOperator U = walkPauliString row := by
  intro tbl c
  have hlam : walkLambda c = 1 := by simp [walkLambda, c]
  have hH : walkHamiltonian tbl c = (walkPauliString row).1 := by
    simp [walkHamiltonian, tbl, c]
  refine ⟨walkPauliString row, walkHamiltonian tbl c, ?_, walkHamiltonian_isHermitian tbl c,
    by rw [sub_self, norm_zero, hlam]; positivity, walkOperator_aux_zero _⟩
  unfold IsQubitizedBlockEncodingUnitary
  simp only []
  rw [walk_basisOutcomeProjector_width_zero, walk_block_zero_embedMatrix, hlam, hH]
  refine ⟨by norm_num, (walkPauliString_isHermitian row).eq, ?_⟩
  simp

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive Walk.Var where | v deriving DecidableEq, Inhabited

open Walk (Var)
open Walk.Var (v)

/-- Number of auxiliary qubits (index, garbage and any sign qubits) of the walk operator for `N`
system qubits, `L` terms and precision `μ`. The reflection acts on all of them. It may not depend
on the table or the coefficients. -/
def walkAux (N L μ : ℕ) : ℕ := sorry

/-- Number of clean ancilla qubits `walkProgram` uses for `N` system qubits, `L` terms and
precision `μ`. It may not depend on the table or the coefficients. -/
def walkAncillas (N L μ : ℕ) : ℕ := sorry

/-- Candidate walk-operator circuit for the table `tbl` and coefficients `c` on `N + walkAux N L μ`
data wires `rData` (`N` system wires followed by the auxiliary wires) and `walkAncillas N L μ`
clean ancilla wires `rAnc`. -/
def walkProgram {n : ℕ} (N L μ : ℕ) (tbl : WalkPauliTable L N) (c : WalkCoeffs L)
    (rData : QRegister (N + walkAux N L μ) n)
    (rAnc : QRegister (walkAncillas N L μ) n) : DynamicCircuit Var n :=
  sorry

open scoped Matrix.Norms.L2Operator in
/-- For all `N`, `L ≥ 1`, `μ`, every table and every coefficient vector with `λ = ∑_j |c_j| > 0`,
there are a self-inverse unitary `U` on system plus auxiliary and a Hermitian `H'` with
`(⟨0|_aux ⊗ 1) U (|0⟩_aux ⊗ 1) = H' / λ` and `‖H' - H‖ ≤ λ / 2^μ` in spectral norm, such that
`walkProgram` acts as the walk operator `(2 |0⟩⟨0|_aux ⊗ 1 - 1) · U` on every input of system
plus auxiliary when the ancillas start in zero, returning the ancillas to zero, across all
disjoint register placements. -/
theorem walk_correctness (N L μ : ℕ) (hL : 1 ≤ L) (tbl : WalkPauliTable L N) (c : WalkCoeffs L)
    (hlam : 0 < walkLambda c) :
    ∃ (U : Unitary (2 ^ (N + walkAux N L μ))) (H' : Operator (2 ^ N)),
      IsQubitizedBlockEncodingUnitary ((walkLambda c : ℚ) : ℝ) H' U ∧
      H'.IsHermitian ∧
      ‖H' - walkHamiltonian tbl c‖ ≤ ((walkLambda c : ℚ) : ℝ) / 2 ^ μ ∧
      ∀ {n : ℕ}
        (rData : QRegister (N + walkAux N L μ) n)
        (rAnc : QRegister (walkAncillas N L μ) n)
        (hdisj : rData.DisjointWires rAnc),
        RealizesCleanSubroutine rData rAnc hdisj (walkOperator U)
          (walkProgram N L μ tbl c rData rAnc).compile := by sorry

/-- `T`-gate count of `walkProgram`. -/
abbrev walkTCount {n : ℕ} (N L μ : ℕ) (tbl : WalkPauliTable L N) (c : WalkCoeffs L)
    (rData : QRegister (N + walkAux N L μ) n)
    (rAnc : QRegister (walkAncillas N L μ) n) : ℕ :=
  (walkProgram N L μ tbl c rData rAnc).count PrimitiveGate.T

/-- Declared qubits: `N` system qubits, `walkAux N L μ` auxiliary qubits and
`walkAncillas N L μ` clean ancillas. -/
abbrev walkQubits (N L μ : ℕ) : ℕ :=
  N + walkAux N L μ + walkAncillas N L μ

/-!
## `T`-Count Cost Theorem

The cost theorem forbids primitive `TOFF` gates and bounds the `T` count by the claimed
`walkTCost N L μ`, for all sizes, every table, every coefficient vector with `λ > 0` and every
register placement.
-/

/-- Claimed `T` count of `walkProgram` for `N` system qubits, `L` terms and precision `μ`. It
depends only on `(N, L, μ)`. -/
def walkTCost (N L μ : ℕ) : ℕ := sorry

/-- For all `N`, `L ≥ 1`, `μ`, every table, every coefficient vector with `λ > 0` and every
register placement, `walkProgram` uses no `TOFF` gates and at most `walkTCost N L μ` `T`
gates. -/
theorem walk_t_cost (N L μ : ℕ) (hL : 1 ≤ L) (tbl : WalkPauliTable L N)
    (c : WalkCoeffs L) (hlam : 0 < walkLambda c) {n : ℕ}
    (rData : QRegister (N + walkAux N L μ) n)
    (rAnc : QRegister (walkAncillas N L μ) n) :
    (walkProgram N L μ tbl c rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      walkTCount N L μ tbl c rData rAnc ≤ walkTCost N L μ := by sorry

/-!
## Spacetime Cost Theorem at the Pinned Size

The cost theorem forbids primitive `TOFF` gates and bounds `T count * qubits` by a closed `ℕ`
constant at `WalkSize.n8l16mu8` (`N = 8` system qubits, `L = 16` terms, `μ = 8`), for every table,
every coefficient vector with `λ > 0` and every register placement.
-/

/-- Sizes of a walk instance: `N` system qubits, `L` terms, precision `μ`. -/
structure WalkSize where
  /-- Number of system qubits. -/
  N : ℕ
  /-- Number of terms. -/
  L : ℕ
  /-- Precision of the block encoding. -/
  μ : ℕ

/-- The pinned size `N = 8`, `L = 16`, `μ = 8`. -/
abbrev WalkSize.n8l16mu8 : WalkSize where
  N := 8
  L := 16
  μ := 8

/-- Claimed spacetime cost (`T count * qubits`) of `walkProgram` at `WalkSize.n8l16mu8`. -/
def walkN8L16Mu8SpacetimeCost : ℕ := sorry

/-- At `WalkSize.n8l16mu8`, for every table, every coefficient vector with `λ > 0` and every
register placement, `walkProgram` uses no `TOFF` gates and has
`T count * (N + auxiliary + ancillas)` at most `walkN8L16Mu8SpacetimeCost`. -/
theorem walk_n8l16mu8_spacetime_cost
    (tbl : WalkPauliTable WalkSize.n8l16mu8.L WalkSize.n8l16mu8.N)
    (c : WalkCoeffs WalkSize.n8l16mu8.L) (hlam : 0 < walkLambda c) {n : ℕ}
    (rData : QRegister (WalkSize.n8l16mu8.N +
      walkAux WalkSize.n8l16mu8.N WalkSize.n8l16mu8.L WalkSize.n8l16mu8.μ) n)
    (rAnc : QRegister (walkAncillas WalkSize.n8l16mu8.N WalkSize.n8l16mu8.L
      WalkSize.n8l16mu8.μ) n) :
    (walkProgram WalkSize.n8l16mu8.N WalkSize.n8l16mu8.L WalkSize.n8l16mu8.μ tbl c rData
        rAnc).count PrimitiveGate.TOFF = 0 ∧
      walkTCount WalkSize.n8l16mu8.N WalkSize.n8l16mu8.L WalkSize.n8l16mu8.μ tbl c rData rAnc *
        walkQubits WalkSize.n8l16mu8.N WalkSize.n8l16mu8.L WalkSize.n8l16mu8.μ ≤
      walkN8L16Mu8SpacetimeCost := by sorry

end QuantumComputation.Specs
