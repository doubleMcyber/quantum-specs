# Roadmap: the primitives quantum algorithms are built from

This file lists the routines that resource estimates for factoring, discrete logarithms and chemistry simulation are assembled from, grouped by layer, and says which have a specification in this repository. It is a working list. Gaps are deliberate invitations: a new specification, or a cheaper solution to an existing one, is a welcome contribution (see "Submitting a better solution" in the README).

Status words:

- **Proved**: a specification and a baseline solution accepted by the Comparator are in this repository.
- **Statement**: a specification is here; no solution yet.
- **Open**: nothing here yet.

In the lower-bounds section, **Proved** means a lower bound on the cost any solution can certify is proved in Lean in this repository. **Closed to leading order** means such a lower bound is proved and its leading term equals that of a verified solution.

The baselines are textbook constructions. Where the table says a better-known construction exists, that construction is an open target for the same frozen statement.

## 1. Arithmetic

| Primitive | Status | Notes |
|---|---|---|
| In-place addition of two registers (Adder) | Proved | Ripple-carry baseline, T count 4(k − 1) |
| Addition of a classical constant (AddConstant) | Proved | |
| Controlled addition (ControlledAdder, ControlledAddConstant) | Proved | |
| Comparison of two registers, and with a constant (Comparator, CompareConstant) | Proved | |
| Subtraction and negation | Open | Follows from the adder; no separate statement yet |
| Multiplication of two quantum registers | Open | |
| Squaring | Open | |
| Division and modular inversion as standalone statements | Open | An inversion is used inside the elliptic-curve solutions |
| Carry-lookahead and other low-depth adders | Open | Needs a depth cost, which the library's cost model does not yet have |

## 2. Modular and field arithmetic

| Primitive | Status | Notes |
|---|---|---|
| Modular addition (ModAdd) | Proved | |
| Modular multiplication by a classical constant (ModMulConst) | Proved | |
| Modular exponentiation (ModExp) | Proved | One multiplication per exponent bit; windowed arithmetic is an open target |
| Prime-field multiplication (FieldMul) | Proved | Schoolbook baseline |
| Montgomery and other reduced-form multipliers | Open | |
| Elliptic-curve point addition, affine (ECPointAdd) | Proved | A lookup witness and a polynomial-cost solution |
| Elliptic-curve point addition, projective mixed (ECPointAddProj) | Proved | A lookup witness and a polynomial-cost solution |
| Windowed scalar multiplication on a curve | Open | |

## 3. Data access

| Primitive | Status | Notes |
|---|---|---|
| Table lookup and its uncomputation (TableLookup) | Proved | Unary iteration, select-swap and measurement-based variants, with and without a qubit budget |
| Lookup with dirty (borrowed) ancillas | Open | |
| Controlled swap of registers as a standalone statement | Open | Used inside several solutions |
| Quantum random-access memory beyond classical tables | Open | |

## 4. State preparation

| Primitive | Status | Notes |
|---|---|---|
| Preparation of a weighted superposition from a classical table (PreparePauliLCU) | Proved | A lookup baseline and an alias-sampling solution |
| Uniform superposition over a number of terms that is not a power of two | Open | Needed for exact preparation at general sizes |
| Preparation with signed or complex amplitudes | Open | |
| Arbitrary state preparation by rotations | Open | Needs a rotation-synthesis cost |

## 5. Simulation building blocks

| Primitive | Status | Notes |
|---|---|---|
| SELECT for a sum of signed Pauli terms (SelectPauli) | Proved | |
| Qubitized walk operator (QubitizedWalk) | Statement | A baseline has been proved outside this release and will be added |
| Controlled qubitized walk (ControlledQubitizedWalk) | Statement | |
| Block encoding of a tensor-hypercontraction Hamiltonian | Open here | A specification exists upstream in formal-quantum-computation (THCFactorization), with no published solution |
| Trotter steps for local Hamiltonians | Open | |
| Givens rotation networks and phase-gradient rotations | Open | |
| Single-qubit rotation synthesis to Clifford + T | Open | |

## 6. Estimation and amplification

| Primitive | Status | Notes |
|---|---|---|
| Phase estimation (PhaseEstimation) | Proved | Query-count cost; baseline by repetition and a vote |
| Amplitude estimation (AmplitudeEstimation) | Proved | |
| Amplitude amplification with a known success probability | Open | |
| Quantum Fourier transform as a costed primitive | Open here | The upstream library verifies a QFT circuit |
| Quantum signal processing and the singular value transformation | Open | |

## 7. Whole algorithms assembled from the above

| Algorithm | Status | Notes |
|---|---|---|
| Order finding for factoring | Open | ModExp and PhaseEstimation are the two ingredients |
| Discrete logarithm on an elliptic curve | Open | Point addition and lookup are the ingredients |
| Ground-state energy by qubitization | Open | PREPARE, SELECT, the walk and phase estimation are the ingredients |

## 8. Lower bounds on cost

| Statement | Status | Notes |
|---|---|---|
| Grover find-any, one marked item, one oracle call per round (Google's specification, cell m = k = 1) | Closed to leading order | Every certified cost is at least (π/8 + 1/4)·√N − 4/√N for N ≥ 4, the leading constant of Google's verified solution (the Fang and Heunen weak-measurement loop). About 1.5 oracle calls at large N remain between the two. See the README |
| The same cell with the constant π/8 + 1/4 | Proved | `findAny_lower_bound_full`. Earlier steps with the constants 3/5 (N ≥ 2^16) and 1/8 (N ≥ 32) remain in the repository. The relCost floor proved at this cell is 12/(5π); the floor 1/2 + 1/π is not yet compiled |
| Grover find-any at the other cells of the grid, and find-all | Open | |
| Lower bounds on the T count of the arithmetic primitives above | Open | |

## 9. Fault tolerance

Nothing in this repository yet. The specifications here count logical T gates and logical qubits. Statements about error-correction gadgets, magic-state factories and compilation onto a code would connect those counts to physical hardware.

## Limits of the format worth knowing before contributing

- Costs are T count and declared qubits. There is no depth, no peak-width and no cost for classical computation.
- A Comparator pass does not by itself show that a cost is a closed-form number or that the program is an explicit circuit. The README describes the extra check used here.
- A frozen helper definition that mentions a hole must be an `abbrev`, or the Comparator rejects a filled solution.
