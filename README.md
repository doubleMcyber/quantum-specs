# Quantum primitive specifications for formal-quantum-computation

This repository contains frozen Lean 4 specifications of quantum arithmetic, table lookup, modular arithmetic, prime-field and elliptic-curve arithmetic, block-encoding and estimation primitives. They are written in the format of Google DeepMind's [formal-quantum-computation](https://github.com/google-deepmind/formal-quantum-computation) library. Seventeen of the nineteen specifications come with a baseline solution whose correctness and cost are proved in Lean. With two extra elliptic-curve solutions and an alias-sampling PREPARE solution there are twenty solution modules, and the Comparator has accepted all twenty.

The specifications and proofs were written with AI coding agents. Lean's kernel and the Comparator checked them.

The repository also contains machine-checked lower bounds for one of Google's own specifications, Grover search with m oracle slots per round and k marked items. For find-any they have the same leading constant as the verified solutions in Google's release in all 121 cells of its grid; for find-all they do so only in the 11 cells with k = 1. They are described under [Lower bounds for Grover search](#lower-bounds-for-grover-search).

## What a specification is

In DeepMind's framework a specification is a Lean file that states a quantum programming problem exactly. It defines the vocabulary of the problem (the encoding of inputs, the ideal unitary, the conditions an input must meet) and leaves holes, written `sorry`, for a solver to fill: a program, an ancilla count, and one claimed cost for each cost theorem. It then states frozen theorems about the filled holes. One theorem says the program is correct: on every placement of its registers in a larger machine, the compiled program acts as the ideal unitary on the data and returns its ancillas to zero. The other theorems bound the cost.

Costs follow the library's resource counting. The T count is the number of T gates. Toffoli gates are not allowed (their count must be zero), so they have to be built from Clifford and T gates. Qubits are the declared registers, data plus ancillas. Where a specification pins a size, the spacetime cost is the T count times the number of declared qubits, and the claim is a single number. A smaller accepted number is a better solution.

Each cost claim has a ChallengeJson that lists the frozen theorems, the holes they depend on, and the permitted axioms (`propext`, `Quot.sound`, `Classical.choice`). The [Comparator](https://github.com/leanprover/comparator), run as `lake comparator`, builds the specification and a solution module, and checks that the solution proves the same frozen statements, fills only the listed holes, uses only the permitted axioms, and passes Lean's kernel.

## What this repository adds

The Google library ships specifications for arcsine, THC factorization, Grover search and several chemistry and materials simulation problems. It has none for the arithmetic, lookup, estimation and block-encoding primitives that factoring, discrete-logarithm and chemistry resource estimates are built from. This repository adds 19 specification modules in seven families.

| Family | Specifications (`QuantumSpecs/<Family>/`) |
|---|---|
| Arithmetic | Adder, AddConstant, ControlledAdder, ControlledAddConstant, Comparator, CompareConstant |
| Lookup | TableLookup (lookup and measurement-based unlookup, with and without a qubit budget) |
| ModularArithmetic | ModAdd, ModMulConst, ModExp |
| PrimeField | FieldMul |
| EllipticCurve | ECPointAdd (affine), ECPointAddProj (projective, mixed coordinates) |
| BlockEncoding | SelectPauli, PreparePauliLCU, QubitizedWalk, ControlledQubitizedWalk |
| Estimation | PhaseEstimation, AmplitudeEstimation |

The specification named Comparator compares two quantum registers. It is unrelated to the Comparator tool.

Baseline solutions are in `QuantumSolutions/<Family>/`, one module per solution. Each elliptic-curve specification has two: a table-lookup solution and a polynomial-cost solution. PreparePauliLCU also has two: the baseline (Hadamards plus a lookup) and an alias-sampling solution in `PreparePauliLCUAlias.lean`. `ChallengeJsons/` holds 70 ChallengeJsons, and `comparator/` holds one Comparator configuration per solution module, the union of its specification's ChallengeJsons, so that one run checks every theorem and hole of the specification.

## Status

Results for the files in this repository. "Baseline cost" is the cost the baseline solution writes into its holes, which its cost theorems prove. The "Comparator" column comes from unsandboxed runs on macOS. The "Sandboxed Linux Comparator" column comes from separate runs of the same files with Lake's bubblewrap sandbox on a Linux cluster. "Hole check" is a separate check, explained below the table.

<!-- BEGIN STATUS TABLE (generated from the project's results; do not edit) -->
| Spec | Baseline cost at pinned sizes | Comparator | Hole check | Sandboxed Linux Comparator |
|---|---|---|---|---|
| TableLookup (lookup, unlookup, budgeted variants) | T 4(2^m − 1), m ancillas; pinned unbudgeted lookup 212,784, unlookup 39,680; budgeted lookup 566,200 (select-swap without unswap), unlookup 147,808 | PASS, unsandboxed (macOS), 2026-11-24 | PASS (2026-11-24) | PASS, sandboxed (Linux, bubblewrap 0.9.0), 2026-11-24 |
| Adder | T 4(k − 1), k ancillas; k=64: 48,384; k=2048: 50,307,072 (T × qubits) | PASS, unsandboxed (macOS), 2026-11-24 | PASS (2026-11-24) | PASS, sandboxed (Linux, bubblewrap 0.9.0), 2026-11-24 |
| AddConstant | T 4(k − 1), 2k ancillas; k=64: 48,384; k=2048: 50,307,072 | PASS, unsandboxed (macOS), 2026-11-24 | PASS (2026-11-24) | PASS, sandboxed (Linux, bubblewrap 0.9.0), 2026-11-24 |
| ControlledAddConstant | T 4(k − 1), 2k ancillas; k=64: 48,636; k=2048: 50,315,260 | PASS, unsandboxed (macOS), 2026-11-24 | PASS (2026-11-24) | PASS, sandboxed (Linux, bubblewrap 0.9.0), 2026-11-24 |
| FieldMul | T 4w²(5w + 1), 2w + 5 ancillas; w=256: 431,511,306,240 | PASS, unsandboxed (macOS), 2026-11-24 | PASS (2026-11-24) | PASS, sandboxed (Linux, bubblewrap 0.9.0), 2026-11-24 |
| ECPointAdd (affine), lookup solution | Lookup baseline (non-vacuity only): T 16 · 2^(2w), 4w ancillas; w=256 constant is `ecAddLookupSpacetime 256` | PASS, unsandboxed (macOS), 2026-11-24 | PASS (2026-11-24) | PASS, sandboxed (Linux, bubblewrap 0.9.0), 2026-11-24 |
| ECPointAdd (affine), polynomial solution | T 16(3w + 28)w²(5w + 1), ancillas `AffPoly.affAnc w`; w=256 spacetime constant 221,200,913,434,411,008 | PASS, unsandboxed (macOS), 2026-11-24 | PASS (2026-11-24) | PASS, sandboxed (Linux, bubblewrap 0.9.0), 2026-11-24 |
| ECPointAddProj (projective mixed), lookup solution | Lookup baseline (non-vacuity only): T 16 · 2^(6w), 12w ancillas; w=256 constant is `ecAddProjLookupSpacetime 256` | PASS, unsandboxed (macOS), 2026-11-24 | PASS (2026-11-24) | PASS, sandboxed (Linux, bubblewrap 0.9.0), 2026-11-24 |
| ECPointAddProj (projective mixed), polynomial solution | T 176w²(5w + 1), 24w + 26 ancillas; w=256 spacetime constant 113,859,882,909,696 | PASS, unsandboxed (macOS), 2026-11-24 | PASS (2026-11-24) | PASS, sandboxed (Linux, bubblewrap 0.9.0), 2026-11-24 |
| PhaseEstimation | General baseline: phaseEstRelCost 48, qubits (m + 3)(6(k + 1) + 1); m=10, k=10 constant 540,672 = 48 · 2^10 · 11 | PASS, unsandboxed (macOS), 2026-11-24 | NA (2026-11-24): the spec itself declares `phaseEstCircuit` `noncomputable`; every other check passes | PASS, sandboxed (Linux, bubblewrap 0.9.0), 2026-11-24 |
| AmplitudeEstimation | General baseline: 6(k + 1) BHMT runs side by side and a median vote; ampEstRelCost 192, at most 192 · 2^m · (k + 1) expected select-oracle calls; m=10, k=10 constant 2,162,688 = 192 · 2^10 · 11 | PASS, unsandboxed (macOS), 2026-11-24 | NA (2026-11-24): the spec itself declares `ampEstCircuit` `noncomputable`; every other check passes | PASS, sandboxed (Linux, bubblewrap 0.9.0), 2026-11-24 |
| ControlledAdder | T 4k + 4(k − 1), 2k ancillas; k=64: T 508, spacetime 130,556; k=2048: T 16,380, spacetime 134,201,340 | PASS, unsandboxed (macOS), 2026-11-24 | PASS (2026-11-24) | PASS, sandboxed (Linux, bubblewrap 0.9.0), 2026-11-24 |
| Comparator | T 8k, k + 3 ancillas; k=64: T 512, spacetime 100,352; k=2048: T 16,384, spacetime 100,728,832 | PASS, unsandboxed (macOS), 2026-11-24 | PASS (2026-11-24) | PASS, sandboxed (Linux, bubblewrap 0.9.0), 2026-11-24 |
| CompareConstant | T 8k, 2k + 3 ancillas; k=64: T 512, spacetime 100,352; k=2048: T 16,384, spacetime 100,728,832 | PASS, unsandboxed (macOS), 2026-11-24 | PASS (2026-11-24) | PASS, sandboxed (Linux, bubblewrap 0.9.0), 2026-11-24 |
| ModAdd | Textbook modular adder: 2b + 5 ancillas, T ≤ 20b; b=2048: T 40,960, spacetime 335,749,120 | PASS, unsandboxed (macOS), 2026-11-24 | PASS (2026-11-24) | PASS, sandboxed (Linux, bubblewrap 0.9.0), 2026-11-24 |
| ModMulConst | In-place multiply by a constant, two passes of controlled modular additions: 5b + 5 qubits; b=2048: T 167,772,160, spacetime 1,718,825,779,200 | PASS, unsandboxed (macOS), 2026-11-24 | PASS (2026-11-24) | PASS, sandboxed (Linux, bubblewrap 0.9.0), 2026-11-24 |
| ModExp | One controlled ModMulConst per exponent bit, 4b + 6 ancillas; l=1280, b=2048: T 214,779,822,080, spacetime 2,475,552,229,294,080 (non-vacuity baseline) | PASS, unsandboxed (macOS), 2026-11-24 | PASS (2026-11-24) | PASS, sandboxed (Linux, bubblewrap 0.9.0), 2026-11-24 |
| SelectPauli | One block per term: b + 1 ancillas, T ≤ 8bL; b=4, N=8, L=16: T 512 on 17 qubits, spacetime 8,704 | PASS, unsandboxed (macOS), 2026-11-24 | PASS (2026-11-24) | PASS, sandboxed (Linux, bubblewrap 0.9.0), 2026-11-24 |
| PreparePauliLCU | Hadamards plus a lookup, not alias sampling: ancillas b + μ + 1, T ≤ 8(b + μ)2^(b + μ); b=4, L=16, μ=8: T 393,216 on 29 qubits, spacetime 11,403,264 | PASS, unsandboxed (macOS), 2026-11-24 | PASS (2026-11-24) | PASS, sandboxed (Linux, bubblewrap 0.9.0), 2026-11-24 |
| PreparePauliLCU, alias-sampling solution | Alias sampling with a coherent alias table (Babbush et al., arXiv:1805.03662, Section III.D): garbage 21, ancillas 11 at b=4, L=16, μ=8: T 140, spacetime 5,040 | PASS, unsandboxed (macOS), 2026-11-24 | PASS (2026-11-24) | PASS, sandboxed (Linux, bubblewrap 0.9.0), 2026-11-24, on this repository's files |
| QubitizedWalk (statement only) | No baseline yet (statement only) | No solution to check; the statement builds (2026-11-24) | n/a (no solution) | n/a (no solution) |
| ControlledQubitizedWalk (statement only) | No baseline yet (statement only) | No solution to check; the statement builds (2026-11-24) | n/a (no solution) | n/a (no solution) |
<!-- END STATUS TABLE -->

A Comparator PASS shows that the solution proves the frozen statements with the permitted axioms. It does not show that a cost hole is a closed-form number or that the program is an explicit circuit: a hole defined by `Classical.choice` over "some correct program of least cost" also passes. The hole check covers that gap. Check C1 requires every hole to be compiled code, not `noncomputable`, and free of `implemented_by`, `extern`, `unsafe`, `opaque` and added axioms. Check C2 requires every natural-number cost hole to reduce to a numeral that the kernel confirms, and every cost function to evaluate at the pinned arguments. The checker that produced this column was written for this project and is not included in this repository. FAIL in that column means a program hole is `noncomputable`; the Comparator result stands.

## Lower bounds for Grover search

`LowerBounds/Grover/` proves lower bounds on the cost that any solution of Google's Grover search specifications (`QuantumComputationSpecs/Algorithms/Grover.lean`) can certify. The specifications pose two problems, find-any and find-all, each on a grid of 121 cells (m, k): m ∈ {1, 2, 4, …, 1024} is the number of oracle slots per round and k ∈ {1, 2, 4, …, 1024} the number of marked items among N = 2^n. For find-any the main theorem has the same leading constant as Google's verified solutions in all 121 cells, so these cells are closed to leading order. For find-all it closes the 11 cells with k = 1 to leading order and leaves the other 110 open.

### What is proved

Fix m, k ≥ 1 and write t = √(2^n/(m k)). Take any oracle circuit of the type the find-any specification asks for, with m oracle slots per round, on any number of qubits. It may measure mid-circuit, branch on classical outcomes, loop and stop adaptively. Suppose that for every set S of k marked items it writes an element of S into the result register with probability 1, from every input state, which is what `groverFindAny_correctness` demands at the cell (m, k). Then every bound on its expected number of oracle rounds that the specification's cost predicate accepts is at least (π/8 + 1/4)·t − 4/t, for every n ≥ 2 + ⌈log2(m k)⌉. The same holds for circuits that meet `groverFindAll_correctness`, which asks that the result register decode to the whole set S.

In Lean, with the definitions in `LowerBounds/Grover/ParallelStatement.lean` and `LowerBounds/Grover/ParallelFullStatement.lean`:

```lean
theorem GroverParallel.fullTargetAny (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) : GroverParallel.FullTargetAny m k
theorem GroverParallel.fullTargetAll (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) : GroverParallel.FullTargetAll m k

def FullTargetAny (m k : ℕ) : Prop :=
  FindAnyLowerBoundMKErr m k (π / 8 + 1 / 4) (errMK m k) (n0full m k)

def FindAnyLowerBoundMKErr (m k : ℕ) (C : ℝ) (E : ℕ → ℝ) (n₀ : ℕ) : Prop :=
  ∀ n ≥ n₀, ∀ (Q : ℕ) (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)),
    MeetsFindAnySpec k c →
    ∀ bound : ℝ,
      AvgOracleCostBound k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦ programOf c S) bound →
      C * √((2 : ℝ) ^ n / ((m : ℝ) * k)) - E n ≤ bound

-- errMK m k n = 4 / √(2 ^ n / (m k)),   n0full m k = 2 + Nat.clog 2 (m * k)
```

`FullTargetAll` and `FindAllLowerBoundMKErr` are the same with `MeetsFindAllSpec` in place of `MeetsFindAnySpec`. `MeetsFindAnySpec k c` and `MeetsFindAllSpec k c` are the postconditions of `groverFindAny_correctness` and `groverFindAll_correctness` for every marked set in `groverTargetSets n k`. `programOf c S` is the program both specifications build from a circuit: reset all qubits, then run `c` compiled with `groverParallelMarkingOracle m S`. `ParallelStatement.lean` proves by `rfl` that the specifications' own programs are `programOf` applied to their circuits, so the theorems bound whatever circuit a solution supplies. The definitions use Google's library unmodified, imported at the commit pinned in `lakefile.toml`, whose specification sources are identical to commit 489edc7 of Google's `main` branch. The hypothesis is weaker than being a solution: it asks for correctness only at the n in question. The theorems hold for all m, k ≥ 1, but Google's benchmark has cells only on the grid.

The cost is the one the specification certifies. `AvgOracleCostBound` asks for a number q(S) for each marked set S such that `CostBound` holds for the program with the oracle of S, and bounds the average of q(S) over the marked sets. `CostBound` requires the expected number of oracle rounds, counted by `CostModel.ofEmbeddedOracle`, to be at most q(S) from every initial state. The bound is therefore an average over the marked set of a worst case over initial states, and it holds for any number a solution could prove in `groverFindAny_rel_cost` or `groverFindAll_rel_cost`. In Google's units, (π/8 + 1/4)·t is (1/2 + 1/π) times `vanillaFindAnyCost n m k` = (π/4)·t.

At the smallest n the statement says nothing. On Google's grid m k is a power of two, so t = 2 at n = 2 + log2(m k) and the right-hand side is about −0.71. From the next n on it is positive: about 0.40 at t = √8, π/2 ≈ 1.57 at t = 4, and within 0.016 of (π/8 + 1/4)·t at t = 256. The corollaries `GroverParallel.findAny_35` and `GroverParallel.findAll_35` give the constant 3/5 with no error term for n ≥ 16 + ⌈log2(m k)⌉, where t ≥ 256.

### Status of the 242 cells

| Problem | Cells | Status |
|---|---|---|
| find-any, every (m, k) | 121 | Closed to leading order |
| find-all, k = 1 | 11 | Closed to leading order |
| find-all, k = 2 and m ≥ 2 | 10 | Not closed; the floor is 51 to 67 percent of Google's leading constant |
| find-all, the other cells with k ≥ 2 | 100 | Not closed; the floor is 0.063 to 45 percent of Google's leading constant |

Closed to leading order means that the proved floor and the cost Google's solution certifies have the same leading term, up to the rounding of Google's rational relCost, which lies less than 1.9·10⁻²¹ above 1/2 + 1/π. It says nothing about the lower-order terms; see the comparison below. The percentages compare the leading constant of the floor with the leading constant of the cost Google's find-all solution certifies in each cell. They are computed from the relCost values in Google's solution files, not proved in Lean.

### Comparison with Google's solutions

Google's find-any solution is a weak-measurement loop. In units of the reference cost it certifies, in every cell, the constant 1/2 + 1/π that Fang and Heunen ([arXiv:2609.39621](https://arxiv.org/abs/2609.39621)) obtained for one marked item and one oracle call per round. The solution (on the `discoveries` branch, written with Gemini) certifies the same rational relCost, 514159265358979323847/628318530717958647692, in all 121 cells. This exceeds 1/2 + 1/π by less than 1.9·10⁻²¹, so the certified cost is (π/8 + 1/4)·t ≈ 0.6427·t to leading order, the constant of the theorem above. Fang and Heunen proved their constant best only within a family of weakly measured loops with one checkpoint. The theorem shows that no program meeting the specification can certify a smaller leading constant in any of the 121 find-any cells. Google's paper reports improvements of up to 2.57 times for parallel search.

The residual gap is lower order. Before rounding to a rational relCost, Google's proof of `groverFindAny_rel_cost` bounds the expected oracle rounds for each marked set by a quantity bd, and a lemma in its solution file (`asymp_schedule_bds`) proves bd ≤ (π/8 + 1/4)·t + 5 for n ≥ 150 + ⌈log2 m⌉ + ⌈log2 k⌉. In that range Google's pre-rounding bound and the floor therefore differ by at most 5 + 4/t rounds per marked set. Evaluated with 120-digit arithmetic (mpmath), bd minus the floor (π/8 + 1/4)·t − 4/t is 1.500000000000 to 12 digits in each of the 121 cells, at every n from 150 + ⌈log2 m⌉ + ⌈log2 k⌉ to 40 above it; a hand expansion at cell (1, 1) gives the limit 3/2. So Google's pre-rounding bound exceeds the lower bound by about 3/2 oracle rounds per marked set at large n. These values were computed, not proved in Lean. Whether any of the gap is real or slack in one of the two proofs is open.

Google scores find-all against `vanillaFindAllCost n m k` = (π/4)·H(k)·√k·t, where H(k) is the sum of 1/√r for r = 1, …, k. At k = 1 this equals the find-any reference, and Google's find-all solution certifies the same rational relCost in the 11 cells with k = 1, so the find-all theorem closes them to leading order in the same sense. The two specifications still differ at k = 1: the find-all postcondition `decodeTargets n 1 (σ res) = S` reads the result modulo 2^n, so it also accepts a result that agrees with the marked item only modulo 2^n, which the find-any postcondition rejects. `fullTargetAll` is proved for the find-all postcondition as written. For k ≥ 2 the theorem gives only the find-any floor (π/8 + 1/4)·t, far below Google's find-all costs: a factor of about 2.2 below at m = 1, k = 2 and about 1,600 below at m = 1, k = 1024. These 110 cells are not closed, and for most of them the floor is not a useful bound.

### The relCost floors

`LowerBounds/Grover/RelCostStatement.lean` turns the four definition holes of the find-any challenge into the fields of a structure `FindAnyFiller` and restates `groverFindAny_correctness` and `groverFindAny_rel_cost` with each hole replaced by the corresponding field (`SolvesFindAny`). `LowerBounds/Grover/RelCostFull.lean` proves

```lean
theorem GroverThreeFifths.relCost_floor_11_full : GroverThreeFifths.RelCostFloor11Full

def RelCostFloor11Full : Prop :=
  ∀ F : FindAnyFiller, SolvesFindAny F → F.cells 1 1 = true →
    (1 / 2 + 1 / π : ℝ) < (F.relCost 1 1 : ℝ)
```

that is, every solution of the challenge that claims cell (1, 1) certifies `groverFindAnyRelCost 1 1` above 1/2 + 1/π ≈ 0.81831. Google's solution certifies a value less than 1.9·10⁻²¹ above that. The proof lets n grow in `findAny_lower_bound_full` (the theorem of the earlier release at cell (1, 1)); equality is excluded because relCost is rational and π is not. The weaker floor `relCost_floor_11` (12/(5π) ≈ 0.764), derived from the 3/5 bound, remains in `RelCost.lean`. The file checks by `rfl` and `Iff.rfl` that Google's own holes, put into a `FindAnyFiller`, give the program `groverFindAnyProgram` and the conjunction of the two theorems as restated in the file.

`LowerBounds/Grover/ParallelRelCostStatement.lean` does the same for every cell and for both challenges: `FindAnyFiller` and `FindAllFiller` hold the four holes of the find-any and the find-all challenge, and `SolvesFindAny` and `SolvesFindAll` restate each challenge's correctness and `rel_cost` theorems with every hole replaced by the corresponding field. The two cell-bookkeeping theorems of each challenge are not assumed. `LowerBounds/Grover/ParallelRelCost.lean` proves

```lean
theorem GroverParallel.relCost_floor_any : GroverParallel.RelCostFloorAny
theorem GroverParallel.relCost_floor_all : GroverParallel.RelCostFloorAll

def RelCostFloorAny : Prop :=
  ∀ F : FindAnyFiller, SolvesFindAny F → ∀ m k : ℕ, 1 ≤ m → 1 ≤ k → F.cells m k = true →
    (1 / 2 + 1 / π : ℝ) < (F.relCost m k : ℝ)

def RelCostFloorAll : Prop :=
  ∀ F : FindAllFiller, SolvesFindAll F → ∀ m k : ℕ, 1 ≤ m → 1 ≤ k → F.cells m k = true →
    ∀ n : ℕ, (π / 8 + 1 / 4) * √((2 : ℝ) ^ n / ((m : ℝ) * k)) ≤
      (F.relCost m k : ℝ) * vanillaFindAllCost n m k
```

The first says that every solution of the find-any challenge certifies `groverFindAnyRelCost m k` above 1/2 + 1/π in every cell (m, k) with m, k ≥ 1 that it claims, which includes every cell of Google's grid. Its proof applies `fullTargetAny` and lets n grow, as at cell (1, 1). In each of the 121 cells, Google's solution certifies a value less than 1.9·10⁻²¹ above the floor.

The second applies `fullTargetAll` in the same way. Because `vanillaFindAllCost n m k` = (π/4)·H(k)·√k·t, it says relCost ≥ (1/2 + 1/π)/(H(k)·√k) in every claimed cell; the inequality is the same at every n. At k = 1 this is the floor 1/2 + 1/π, stated without strict inequality. For k ≥ 2 it is only the find-any floor expressed in find-all units, and it is weak: by the comparison in the table above, it is 0.063 percent (m = 1, k = 1024) to 67 percent of the relCost that Google's find-all solution certifies in the same cell.

Both theorems say something only if some filler satisfies `SolvesFindAny` or `SolvesFindAll`. This repository contains no such filler. That Google's solutions are one rests on Google's solution files on the `discoveries` branch, which this library does not import or check. The examples at the end of `ParallelRelCostStatement.lean` check, for Google's own holes put into a filler, that its programs are `groverFindAnyProgram` and `groverFindAllProgram` (`rfl`), that `SolvesFindAny` and `SolvesFindAll` unfold to the restated theorems (`Iff.rfl`), and that the types of Google's four challenge theorems are exactly the conjuncts of `SolvesFindAny` and `SolvesFindAll`. The specification leaves those theorems open, so the examples check types, not proofs. The statements `RelCostFloorAny` and `RelCostFloorAll` were reviewed against Google's specification by an AI agent that did not write them, which found them faithful with the caveats above; no human has reviewed them.

### Earlier steps

Three statements at the cell m = k = 1 remain in the repository from earlier releases. `GroverThreeFifths.findAny_lower_bound_full` (`FullBound.lean`) is the find-any bound above at m = k = 1, (π/8 + 1/4)·√N − 4/√N for N ≥ 4, stated with `FindAnyLowerBoundErr` from `FullStatement.lean`. The other two use `FindAnyLowerBound C n₀` from `Statement.lean`, which says that every accepted bound is at least C·√N for every n ≥ n₀:

```lean
theorem GroverThreeFifths.findAny_lower_bound_35 : GroverLowerBound.FindAnyLowerBound (3 / 5) 16
theorem GroverLowerBound.findAny_lower_bound : GroverLowerBound.FindAnyLowerBound (1 / 8) 5
```

The 3/5 bound (N ≥ 2^16) is in `ThreeFifthsBound.lean` and the 1/8 bound (N ≥ 32) in `EighthBound.lean`. The 3/5 proof reuses the lemmas of the 1/8 proof, and the full-constant proof (`FullPotential.lean`, `FullQuery.lean`, `FullBound.lean`) keeps the assembly of the 3/5 proof and replaces its potential function and its oracle-step lemma. The proof at every cell (`ParallelDefs.lean` to `ParallelBound.lean`) keeps the assembly of `FullBound.lean` with the marked sets of `groverTargetSets n k` as the run index, one run per marked set instead of one per marked item, and an oracle-step lemma for the m-slot oracle (`ParallelOracle.lean`).

### What is not proved

- Matching lower-order terms. The two sides agree only to leading order. Google's own lemma leaves at most 5 + 4/t oracle rounds per marked set between its certified bound and the floor, and the computed gap is about 3/2 rounds at large n. The theorems do not rule out a solution that certifies a cost inside that gap, below Google's.
- Find-all with k ≥ 2. The 110 cells have only the find-any floor, which is 0.063 to 67 percent of Google's leading constant.
- Small n. The statement is empty at n = 2 + log2(m k), and at the next n it gives only about 0.40 oracle rounds.
- Other cost measures. The cost is Google's certified bound, a worst case over the initial state averaged over the marked sets. A bound averaged over initial states as well, for example, is not covered.
- The figures computed from Google's solution files: the residual gap, the per-cell relCost values and the find-all percentages.

### How it was made and checked

The proofs were written with AI coding agents and checked by Lean. The statements were reviewed by AI agents; no human expert has reviewed the statements or the proofs. The statements of `fullTargetAny`, `fullTargetAll`, `findAny_35` and `findAll_35` were reviewed twice against Google's specification, the second time by an agent that had not worked on the proofs. Both reviews found the statements faithful to the specification, with the caveats stated above: empty at the smallest n, weak for find-all at k ≥ 2, a find-all postcondition at k = 1 that differs from find-any's, and closure only to leading order. The statement `RelCostFloor11Full` was reviewed separately by an agent that had not worked on its proof and found faithful, and `RelCostFloorAny` and `RelCostFloorAll` by another agent that had not written them, with the result stated above. `checks/GroverAxioms.lean` prints the statements and the axioms of the theorems above; the expected axioms are `propext`, `Classical.choice` and `Quot.sound`.

The files are copies of the project's working files in which only comments, module names, imports and namespace names changed; the export tool checked this mechanically by comparing the files with all comments removed. The working files of the proof at every cell included their own copies of the proof at cell (1, 1). The export tool checked that these copies are byte-identical to the files already published here, so they are not published twice and the new files import the existing ones. The project also has a file that applies the general theorems to each of the 242 cells (75 KB). It is left out: each instance only substitutes one cell's numbers into the general theorem and adds no statement beyond it. The library is compiled with Lean's default `autoImplicit` and `maxSynthPendingDepth` settings, under which it was developed (see `lakefile.toml`).

### Prior work

We did not find the matching bound, or any lower bound with a constant above π/8 for this model, stated in the literature. Our search was made for the cell m = k = 1 and was limited: general web searches, arXiv abstract metadata, and the citation records of OpenAlex and INSPIRE, over about a day, without full-text search of arXiv. Some sources were judged from their abstracts or from search snippets only, and a paper posted in the last few days or using other terms would have been missed. We did not repeat the search for several oracle slots per round or several marked items. This is a report of what we found, not a claim of priority.

- Zalka ([quant-ph/9711070](https://arxiv.org/abs/quant-ph/9711070)) showed that no algorithm beats Grover's algorithm for a fixed number of queries. Applied to algorithms truncated after t queries, exact bounds of that kind (also Dohotaru and Høyer, [arXiv:0810.3647](https://arxiv.org/abs/0810.3647)) give about (π/8)·√N for the expected number of queries; we did not find this derivation written out. Zalka also notes that measuring and restarting saves about 12 percent of the queries (about 0.690·√N), without claiming that nothing does better.
- Montanaro ([arXiv:0908.3066](https://arxiv.org/abs/0908.3066), Proposition 2.3) proves an expected-query lower bound of about 0.206·√N for zero-error search with intermediate measurements.
- Fang and Heunen ([arXiv:2609.39621](https://arxiv.org/abs/2609.39621)) give a weakly measured loop with (π/8 + 1/4 + o(1))·√N expected Grover iterations and show that no loop in a family of weakly measured loops with one checkpoint does better. They make no such claim for all algorithms. In OpenAlex and INSPIRE the only work citing it was Google's paper ([arXiv:2611.09822](https://arxiv.org/abs/2611.09822)).
- Andrés-Martínez and Heunen ([arXiv:2009.08832](https://arxiv.org/abs/2009.08832)) introduced weakly measured while loops for search, an earlier algorithm of the same kind; we judged it from its abstract and snippets and saw no lower bound for all programs.
- Belovs and Yolcu ([arXiv:2301.02003](https://arxiv.org/abs/2301.02003)) characterize Las Vegas query complexity, in a model with query skipping, by the adversary bound. We did not find an explicit constant for search derived from their result, and their measure is not the cost of the specification.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain (Lean v4.35.0) is pinned in `lean-toolchain`. Then:

```bash
git clone <this repository>
cd <this repository>
lake exe cache get                       # downloads Mathlib's prebuilt files
lake build                               # builds every specification
lake build QuantumSolutions              # builds every solution
lake build QuantumSolutions.Arithmetic.Adder   # builds one solution
lake build LowerBounds                   # builds the Grover lower bounds
lake env lean checks/GroverAxioms.lean   # prints the theorems and their axioms
```

Google's library has no prebuilt cache, so the first build compiles its modules from source.

To check a solution with the Comparator, on Linux with [bubblewrap](https://github.com/containers/bubblewrap) installed:

```bash
lake comparator --config comparator/Adder.json
```

The run passes when it prints `Your solution is okay!`. The sandbox needs bubblewrap, which exists only on Linux. On macOS the Comparator runs only unsandboxed, with `lake comparator --inadvisably-no-sandbox --config comparator/Adder.json`; an unsandboxed run trusts the solution's build not to tamper with the check.

These steps were tested on 2026-11-24 on a Linux x86_64 cluster node, starting from a fresh copy of this repository's files, with elan and Lean 4.35.0 installed fresh and empty Lake and Mathlib caches. `lake exe cache get` fetched every dependency from GitHub at the revisions in `lake-manifest.json` and downloaded Mathlib's prebuilt files (about 2 minutes). `lake build` built the 19 specifications (about 2 minutes) and `lake build QuantumSolutions` built the 20 solutions (about 5 minutes on 8 cores). The sandboxed Comparator then passed on five configurations, each in about 2 minutes: PreparePauliLCUAlias, Adder, TableLookup, SelectPauli and ECPointAddProjPoly. The other fifteen configurations were not rerun from this fresh copy.

The lower-bound library was tested the same way in job 2021850 on a Linux x86_64 cluster node with 8 cores, from a fresh copy of this repository's files with elan, Lean 4.35.0 and the caches installed fresh. It started on 2026-11-25 (US Pacific time) and ran for 9 minutes 47 seconds. `lake exe cache get` took 158 seconds and fetched the dependencies at the revisions in `lake-manifest.json`. `lake build LowerBounds` took 291 seconds, which includes compiling the needed parts of Google's library, and built all 30 modules without errors and without `sorry` (with deprecation and linter warnings). `lake env lean checks/GroverAxioms.lean` took 30 seconds. Besides the printed definitions, which match the statements quoted above, it reported

```
GroverThreeFifths.findAny_lower_bound_35 : GroverLowerBound.FindAnyLowerBound (3 / 5) 16
'GroverThreeFifths.findAny_lower_bound_35' depends on axioms: [propext, Classical.choice, Quot.sound]
'GroverLowerBound.findAny_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
GroverThreeFifths.findAny_lower_bound_full : GroverThreeFifths.FullConstantTarget
'GroverThreeFifths.findAny_lower_bound_full' depends on axioms: [propext, Classical.choice, Quot.sound]
GroverThreeFifths.relCost_floor_11 : GroverThreeFifths.RelCostFloor11
'GroverThreeFifths.relCost_floor_11' depends on axioms: [propext, Classical.choice, Quot.sound]
GroverThreeFifths.relCost_floor_11_full : GroverThreeFifths.RelCostFloor11Full
'GroverThreeFifths.relCost_floor_11_full' depends on axioms: [propext, Classical.choice, Quot.sound]
GroverParallel.fullTargetAny : ∀ (m k : ℕ), 1 ≤ m → 1 ≤ k → GroverParallel.FullTargetAny m k
'GroverParallel.fullTargetAny' depends on axioms: [propext, Classical.choice, Quot.sound]
GroverParallel.fullTargetAll : ∀ (m k : ℕ), 1 ≤ m → 1 ≤ k → GroverParallel.FullTargetAll m k
'GroverParallel.fullTargetAll' depends on axioms: [propext, Classical.choice, Quot.sound]
GroverParallel.findAny_35 : ∀ (m k : ℕ),
  1 ≤ m → 1 ≤ k → GroverParallel.FindAnyLowerBoundMK m k (3 / 5) (GroverParallel.n0_of m k)
'GroverParallel.findAny_35' depends on axioms: [propext, Classical.choice, Quot.sound]
GroverParallel.findAll_35 : ∀ (m k : ℕ),
  1 ≤ m → 1 ≤ k → GroverParallel.FindAllLowerBoundMK m k (3 / 5) (GroverParallel.n0_of m k)
'GroverParallel.findAll_35' depends on axioms: [propext, Classical.choice, Quot.sound]
GroverParallel.relCost_floor_any : GroverParallel.RelCostFloorAny
'GroverParallel.relCost_floor_any' depends on axioms: [propext, Classical.choice, Quot.sound]
GroverParallel.relCost_floor_all : GroverParallel.RelCostFloorAll
'GroverParallel.relCost_floor_all' depends on axioms: [propext, Classical.choice, Quot.sound]
```

In the same job, four files outside this repository were checked. The first checked that Google's own `groverFindAny_correctness` and `groverFindAny_rel_cost` type-check as a proof of `GroverThreeFifths.SolvesFindAny` for Google's holes, so for Google's holes the restatement in that definition is the two challenge theorems as compiled from Google's specification. The second and third checked the same for `GroverParallel.SolvesFindAny` and, with Google's two find-all theorems, for `GroverParallel.SolvesFindAll`, as the examples in `ParallelRelCostStatement.lean` also do. The fourth checked that Google's `groverFindAny_correctness` and `groverFindAll_correctness` give `MeetsFindAnySpec` and `MeetsFindAllSpec` for Google's circuits in every cell of its grid (for n ≥ 1 and k ≤ 2^n), so the lower bounds apply to those circuits.

`lake exe cache get` needs the `leantar` program that the Lean 4.35.0 toolchain ships in its `bin` directory. If it reports that `leantar` was not found, reinstall the toolchain with elan.

## Dependencies

| Dependency | Pinned revision |
|---|---|
| google-deepmind/formal-quantum-computation, `discoveries` branch | `a88de8ff65d78af564b2373088ca369dc95f6547` |
| google-deepmind/formal-quantum-computation, `main` branch (same library sources) | `489edc7039aa4cdded53724b39ea90e33d2c88b4` |
| Lean | v4.35.0 |
| Mathlib, Physlib and their dependencies | as in `lake-manifest.json` (Mathlib and Physlib at their `v4.35.0` tags) |

Lake can require only one revision of a package, so `lakefile.toml` requires the `discoveries` commit by git URL. Between the two commits, the `QuantumComputation` and `QuantumComputationSpecs` Lean sources are identical; `discoveries` adds the `QuantumComputationDiscoveries` library and changes six ChallengeJsons, the lakefile and one script. The specifications import only `QuantumComputation`, `QuantumComputationSpecs` (the two walk specifications reuse definitions from the THC factorization specification) and Mathlib, so they would build against `main` alone. Nine solutions (the six arithmetic and three modular-arithmetic ones) import the ripple-carry adder from `QuantumComputationDiscoveries.Primitives.Arcsin.Solution.EqualTableAdd`, which is only on `discoveries`.

## Limits

Two kinds of Comparator run stand behind the table. Every solution passed unsandboxed on macOS (`--inadvisably-no-sandbox`), where nothing stops a solution's build from interfering with the check. Nineteen of the twenty also passed in Lake's bubblewrap sandbox on Linux (Lean 4.35.0, bubblewrap 0.9.0), on the project's copies of these files, which differ from the files here only in comments. The alias-sampling PREPARE solution was added after that run; its sandboxed result comes from the fresh-copy test described under Building, which ran on exactly the files in this repository. Both kinds can be repeated by anyone with the commands above.

Two checks cannot be repeated from this repository. The hole check was run with a checker written for this project that is not included here, so its column has to be taken on trust or redone with another verifier. The adversarial attacks summarized below were compiled Lean files kept outside this repository; only their conclusions are reported.

The baselines show that each specification can be met. They are textbook constructions, and some are deliberately expensive witnesses: the elliptic-curve table-lookup solutions have cost exponential in the bit length, and the ModExp baseline is a plain one-multiplication-per-exponent-bit construction. None of the baseline costs is a record or an optimized result.

QubitizedWalk and ControlledQubitizedWalk are statements only in this release: it contains no solution for either, so nothing here shows that they can be satisfied at the benchmark size μ = 8. A baseline for QubitizedWalk has been proved since and will be added in the next version, together with a larger pinned size for PreparePauliLCU. PhaseEstimation and AmplitudeEstimation pass the Comparator but get NA in the hole check, because each specification declares its own circuit hole `noncomputable`.

The cost model is the library's. Classical computation and the evaluation of classical conditions cost nothing, and qubits are counted as declared registers, not as peak width. The authors' own review of the modular-arithmetic specifications noted that a solution may use classical precomputation about the instance and that the specifications cannot observe a global phase. QubitizedWalk cannot tell a Hamiltonian H from −H for the same reason, which is why ControlledQubitizedWalk exists. Where a cost theorem pins a size, a solution may branch on the parameters and use a different construction at the pinned instance than elsewhere; the theorems stated for every size still constrain it everywhere.

Each specification was meant to be attacked by a reviewer trying to satisfy it with a program no physicist would accept (free classical computation, undeclared qubits, a vacuous precondition, an answer hidden in a parameter). Coverage at this release is incomplete:

- ModAdd, ModMulConst and ModExp were attacked with compiled attempts on this version, with no successful attack. The compiled facts confirm the documented encodings and show that a program doing nothing meets ModAdd only in the degenerate case N = 1.
- SelectPauli and PreparePauliLCU were attacked with compiled attempts on this version, with no successful attack. Two documented properties were compiled: both of the library's correctness predicates leave the global phase free, and at b = 1, L = 2 a PREPARE program whose index register is fully entangled with the garbage register passes. That no program short of the task meets the costs at the pinned sizes was argued, not compiled. The alias-sampling solution has not been audited on its own; it is checked against the same frozen specification.
- QubitizedWalk and ControlledQubitizedWalk were attacked with compiled attempts on this version, with no successful attack at the benchmark size μ = 8. Two weaknesses were compiled. At μ = 0 a program that ignores its data meets the body of QubitizedWalk's correctness theorem for every input. In ControlledQubitizedWalk, U and −U are both admissible whenever the zero operator fits the error budget, so the sign of the controlled block is not pinned in those cases.
- AmplitudeEstimation was read by an independent reviewer and attacked with compiled attempts on this version. No attempt met all theorems of a ChallengeJson. Two weaknesses were compiled: the correctness theorem can be met without any oracle query in the small cases m ≤ 1, k = 0, n = 0 and m = 2 with k = 1, and the cost theorem charges nothing for branches that abort or diverge. The pinned size m = 10, k = 10 is not one of the query-free cases.
- TableLookup and Adder were attacked with compiled attempts on earlier versions, with no successful attack. TableLookup's budgeted variants came after that attack and have not been attacked; this version, budgeted variants included, was read by an independent reviewer who found no way to meet a correctness theorem without doing the lookup. The Adder version attacked differs from this one only in two helper definitions changed from `def` to `abbrev`, which does not change their meaning.
- FieldMul, ECPointAddProj, ControlledAdder, Comparator and CompareConstant were read by an independent reviewer on this version, without a compiled attack. The reviewer found no way to meet a correctness theorem without doing the task.
- AddConstant, ControlledAddConstant, ECPointAdd and PhaseEstimation were read by an independent reviewer on earlier versions, without a compiled attack.

Every "no successful attack" above leans on one argument: a program that satisfies the library's correctness predicate acts as the exact unitary channel on valid inputs with clean ancillas. The reviewer proved this in Lean during the review, in expectation form, for every program including ones that loop or abort.

## Roadmap

`ROADMAP.md` lists the primitives that factoring, discrete-logarithm and chemistry resource estimates are built from, layer by layer, and marks which have a specification and a proved baseline here and which are open.

## Submitting a better solution

1. Copy the baseline module, for example `QuantumSolutions/Arithmetic/Adder.lean`, to a new module such as `QuantumSolutions/Arithmetic/AdderYourName.lean`. A solution restates the whole specification in the namespace `QuantumComputation.Specs`, fills the holes and proves the frozen theorems. It does not import the specification module. Leave every declaration that is not a hole exactly as it is: the Comparator compares the compiled declarations, including their reducibility, which is why frozen helper definitions that mention a hole are `abbrev`s.
2. Fill the holes with your construction and a smaller cost. Make the program a computable definition and each cost hole a closed number, provable by `rfl` or `decide` at the pinned sizes, so that the result is a circuit and a number rather than an existence proof.
3. Copy `comparator/Adder.json` to `comparator/AdderYourName.json` and set `solution_module` to your module.
4. Run `lake build QuantumSolutions.Arithmetic.AdderYourName` and `lake comparator --config comparator/AdderYourName.json` on Linux, so that the run is sandboxed.
5. Open a pull request with the module, the configuration and the full Comparator output.

A change to a specification's statement is a new specification and needs a new baseline proof.

## Credits and licence

This work builds on Google DeepMind's [formal-quantum-computation](https://github.com/google-deepmind/formal-quantum-computation), released under the Apache License 2.0 and described in S. Shirobokov et al., "Discovering formally verified quantum programs with AI", [arXiv:2611.09822](https://arxiv.org/abs/2611.09822) (2026). The specification format, the circuit and resource-counting framework, the correctness predicates and the Comparator workflow are theirs. Nine solution files contain sections copied from the `discoveries` branch of that repository, marked `GOOGLE-DERIVED`; each names Google LLC in its header and states its modifications, and `NOTICE` lists them. `LowerBounds/Grover/Statement.lean` restates three definitions from Google's Grover specification in the same way, `LowerBounds/Grover/RelCostStatement.lean` restates the challenge's hole types, its program construction and the statements of two of its theorems, `LowerBounds/Grover/ParallelStatement.lean` restates the program construction, both postconditions and both cost predicates for any number of oracle slots and marked items, and `LowerBounds/Grover/ParallelRelCostStatement.lean` restates the hole types, the program constructions and the statements of the correctness and `rel_cost` theorems of both challenges. This repository is not affiliated with or endorsed by Google DeepMind.

Copyright 2026 Marlon Moenius. Licensed under the Apache License, Version 2.0; see `LICENSE`.
