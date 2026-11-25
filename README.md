# Quantum primitive specifications for formal-quantum-computation

This repository contains frozen Lean 4 specifications of quantum arithmetic, table lookup, modular arithmetic, prime-field and elliptic-curve arithmetic, block-encoding and estimation primitives. They are written in the format of Google DeepMind's [formal-quantum-computation](https://github.com/google-deepmind/formal-quantum-computation) library. Seventeen of the nineteen specifications come with a baseline solution whose correctness and cost are proved in Lean. With two extra elliptic-curve solutions and an alias-sampling PREPARE solution there are twenty solution modules, and the Comparator has accepted all twenty.

The specifications and proofs were written with AI coding agents. Lean's kernel and the Comparator checked them.

The repository also contains a machine-checked lower bound for one of Google's own specifications, Grover find-any search with one marked item and one oracle call per round, whose leading constant matches the verified solution in Google's release. It is described under [Lower bound for Grover find-any search](#lower-bound-for-grover-find-any-search).

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

## Lower bound for Grover find-any search

`LowerBounds/Grover/` proves lower bounds on the cost that any solution of Google's Grover find-any specification (`QuantumComputationSpecs/Algorithms/Grover.lean`) can certify in the cell m = k = 1, that is, one marked item among N = 2^n and one oracle call per round. The main theorem has the same leading constant as the verified solution in Google's release, so this cell is closed to leading order.

### What is proved

Take any oracle circuit of the type the specification asks for at m = k = 1, on any number of qubits. It may measure mid-circuit, branch on classical outcomes, loop and stop adaptively. Suppose it returns the marked item with probability 1, from every input state and for every choice of marked item, which is what `groverFindAny_correctness` demands. Then every bound on its expected number of oracle calls that the specification's cost predicate accepts is at least (π/8 + 1/4)·√N − 4/√N, for every N ≥ 4.

In Lean, with the definitions in `LowerBounds/Grover/FullStatement.lean`:

```lean
theorem GroverThreeFifths.findAny_lower_bound_full : GroverThreeFifths.FullConstantTarget

def FullConstantTarget : Prop :=
  FindAnyLowerBoundErr (π / 8 + 1 / 4) (fun n ↦ 4 / √((2 : ℝ) ^ n)) 2

def FindAnyLowerBoundErr (C : ℝ) (E : ℕ → ℝ) (n₀ : ℕ) : Prop :=
  ∀ n ≥ n₀, ∀ (Q : ℕ) (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1)),
    MeetsFindAnySpec c →
    ∀ bound : ℝ,
      AvgOracleCostBound 1
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle 1 S))
        (fun S ↦ findAnyProgramOf c S) bound →
      C * √((2 : ℝ) ^ n) - E n ≤ bound
```

`MeetsFindAnySpec c` and `findAnyProgramOf c S` are defined in `LowerBounds/Grover/Statement.lean`. `MeetsFindAnySpec c` is the postcondition of `groverFindAny_correctness` at m = k = 1 for every one-element marked set, and `findAnyProgramOf c S` is the program `groverFindAnyProgram` builds from the circuit (reset all qubits, then run `c` compiled with the marking oracle of S). That file also proves by `rfl` that the specification's own program at the cell (1, 1) is `findAnyProgramOf` applied to its circuit, so the theorem bounds whatever circuit a solution supplies. The definitions use Google's library unmodified, imported at the commit pinned in `lakefile.toml`. The new declarations are in the namespace `GroverThreeFifths`, with the 3/5 theorem whose lemmas they reuse.

The cost is the one the specification certifies. `AvgOracleCostBound` asks for a number q(S) for each marked set S such that `CostBound` holds for the program with the oracle of S, and bounds the average of q(S) over S. `CostBound` requires the expected number of oracle calls, counted by `CostModel.ofEmbeddedOracle`, to be at most q(S) from every initial state. The bound is therefore an average over the marked item of a worst case over initial states, and it holds for any number a solution could prove in `groverFindAny_rel_cost`.

The error term is 4/√N. At N = 4 the right-hand side is about −0.71, so the statement says nothing there. It is positive from N = 8 on: about 0.40 at N = 8, π/2 ≈ 1.57 at N = 16, and within 0.016 of (π/8 + 1/4)·√N at N = 2^16.

### Comparison with Google's solution

Google's verified solution for this specification (on the `discoveries` branch, written with Gemini) claims `groverFindAnyRelCost 1 1` close to 1/2 + 1/π against the reference scale (π/4)·√N, which is a cost of (π/8 + 1/4)·√N ≈ 0.6427·√N plus lower-order terms, proved for large n. That is the leading constant of the theorem above. The algorithm at this cell is the weak-measurement loop of Fang and Heunen ([arXiv:2609.39621](https://arxiv.org/abs/2609.39621)), which Google's paper says its verified circuit matches. Google's paper reports improvements of up to 2.57 times over prior baselines for parallel search; at this cell its verified solution has the published Fang and Heunen constant, so no such gain is claimed here.

The theorem shows that the Fang and Heunen constant is optimal to leading order over all programs that meet the specification. Their paper proved its optimality only within a restricted family, weakly measured loops with one checkpoint.

The residual gap is lower order. Before rounding to a rational relCost, Google's proof of `groverFindAny_rel_cost` bounds the expected oracle calls for each marked set by a quantity bd(N), and its Lean file proves bd(N) ≤ (π/8 + 1/4)·√N + 5 for n ≥ 150. Evaluated in double-precision floating point, bd(N) − (π/8 + 1/4)·√N is 2.52 at N = 8 (its largest value), 1.502 at N = 2^16 and 1.50000 from N = 2^40 to N = 2^100; a hand expansion gives the limit 3/2. So Google's pre-rounding bound exceeds the lower bound by about 1.5 oracle calls at large N, and by at most about 3.9 calls for N ≥ 4. These values were computed in floating point and are not proved in Lean. Whether any of the gap is real or slack in one of the two proofs is open.

### The relCost corollary

`LowerBounds/Grover/RelCostStatement.lean` turns the four definition holes of the challenge into the fields of a structure `FindAnyFiller` and restates `groverFindAny_correctness` and `groverFindAny_rel_cost` with each hole replaced by the corresponding field (`SolvesFindAny`). `LowerBounds/Grover/RelCost.lean` proves

```lean
theorem GroverThreeFifths.relCost_floor_11 : GroverThreeFifths.RelCostFloor11

def RelCostFloor11 : Prop :=
  ∀ F : FindAnyFiller, SolvesFindAny F → F.cells 1 1 = true →
    (12 / (5 * π) : ℝ) < (F.relCost 1 1 : ℝ)
```

that is, every solution of the challenge that claims cell (1, 1) certifies `groverFindAnyRelCost 1 1` above 12/(5π) ≈ 0.764. Google's solution certifies about 0.818. The proof derives the floor from the 3/5 theorem below; equality is excluded because relCost is rational and π is not. The file checks by `rfl` and `Iff.rfl` that Google's own holes, put into a `FindAnyFiller`, give the program `groverFindAnyProgram` and the conjunction of the two theorems as restated in the file.

The stronger floor relCost 1 1 > 1/2 + 1/π, which matches Google's value to leading order, is not included. Its statement exists in the project's working files, but its proof had not been compiled when this release was made. Google's certified relCost exceeds 1/2 + 1/π by less than 1.9·10⁻²¹.

### Earlier steps

Two weaker theorems remain in the repository. They use `FindAnyLowerBound C n₀` from `Statement.lean`, which is `FindAnyLowerBoundErr` without the error term: every accepted bound is at least C·√N for every n ≥ n₀.

```lean
theorem GroverThreeFifths.findAny_lower_bound_35 : GroverLowerBound.FindAnyLowerBound (3 / 5) 16
theorem GroverLowerBound.findAny_lower_bound : GroverLowerBound.FindAnyLowerBound (1 / 8) 5
```

The 3/5 bound (N ≥ 2^16) is in `ThreeFifthsBound.lean` and the 1/8 bound (N ≥ 32) in `EighthBound.lean`. The 3/5 proof reuses the lemmas of the 1/8 proof, and the full-constant proof (`FullPotential.lean`, `FullQuery.lean`, `FullBound.lean`) keeps the assembly of the 3/5 proof and replaces its potential function and its oracle-step lemma.

### What is not proved

- Exact optimality. The two sides agree only to leading order, and about 1.5 oracle calls separate Google's pre-rounding bound from the lower bound at large N. The theorem does not rule out a solution that certifies a cost inside that gap, below Google's.
- Only the cell m = k = 1 of find-any is covered. The other 120 cells of the grid and the find-all specification have no lower bound here.
- Nothing is proved about small N beyond what the statement gives: it is empty at N = 4, and at N = 8 it gives only about 0.40 oracle calls.
- The cost is Google's certified bound, a worst case over the initial state averaged over the marked item. Other cost measures, such as a bound averaged over initial states as well, are not covered.
- The relCost floor proved in Lean is 12/(5π), not 1/2 + 1/π.

### How it was made and checked

The proofs were written with AI coding agents and checked by Lean. The statements were reviewed by AI agents; no human expert has reviewed the statements or the proofs. `checks/GroverAxioms.lean` prints the statements and the axioms of the theorems above; the expected axioms are `propext`, `Classical.choice` and `Quot.sound`. The files are copies of the project's working files in which only comments, module names, imports and the two namespace names changed; the export tool checked this mechanically by comparing the files with all comments removed. The library is compiled with Lean's default `autoImplicit` and `maxSynthPendingDepth` settings, under which it was developed (see `lakefile.toml`).

### Prior work

We did not find the matching bound, or any lower bound with a constant above π/8 for this model, stated in the literature. Our search was limited: general web searches, arXiv abstract metadata, and the citation records of OpenAlex and INSPIRE, over about a day, without full-text search of arXiv. Some sources were judged from their abstracts or from search snippets only, and a paper posted in the last few days or using other terms would have been missed. This is a report of what we found, not a claim of priority.

- Zalka ([quant-ph/9711070](https://arxiv.org/abs/quant-ph/9711070)) showed that Grover's algorithm is optimal for a fixed number of queries. Applied to algorithms truncated after t queries, exact bounds of that kind (also Dohotaru and Høyer, [arXiv:0810.3647](https://arxiv.org/abs/0810.3647)) give about (π/8)·√N for the expected number of queries; we did not find this derivation written out. Zalka also notes that measuring and restarting saves about 12 percent of the queries (about 0.690·√N), without claiming that this is optimal.
- Montanaro ([arXiv:0908.3066](https://arxiv.org/abs/0908.3066), Proposition 2.3) proves an expected-query lower bound of about 0.206·√N for zero-error search with intermediate measurements.
- Fang and Heunen ([arXiv:2609.39621](https://arxiv.org/abs/2609.39621)) give a weakly measured loop with (π/8 + 1/4 + o(1))·√N expected Grover iterations and show that it is optimal within a family of weakly measured loops with one checkpoint. They do not claim optimality over all algorithms. In OpenAlex and INSPIRE the only work citing it was Google's paper ([arXiv:2611.09822](https://arxiv.org/abs/2611.09822)).
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
lake env lean checks/GroverAxioms.lean   # prints the main theorem and its axioms
```

Google's library has no prebuilt cache, so the first build compiles its modules from source.

To check a solution with the Comparator, on Linux with [bubblewrap](https://github.com/containers/bubblewrap) installed:

```bash
lake comparator --config comparator/Adder.json
```

The run passes when it prints `Your solution is okay!`. The sandbox needs bubblewrap, which exists only on Linux. On macOS the Comparator runs only unsandboxed, with `lake comparator --inadvisably-no-sandbox --config comparator/Adder.json`; an unsandboxed run trusts the solution's build not to tamper with the check.

These steps were tested on 2026-11-24 on a Linux x86_64 cluster node, starting from a fresh copy of this repository's files, with elan and Lean 4.35.0 installed fresh and empty Lake and Mathlib caches. `lake exe cache get` fetched every dependency from GitHub at the revisions in `lake-manifest.json` and downloaded Mathlib's prebuilt files (about 2 minutes). `lake build` built the 19 specifications (about 2 minutes) and `lake build QuantumSolutions` built the 20 solutions (about 5 minutes on 8 cores). The sandboxed Comparator then passed on five configurations, each in about 2 minutes: PreparePauliLCUAlias, Adder, TableLookup, SelectPauli and ECPointAddProjPoly. The other fifteen configurations were not rerun from this fresh copy.

The lower-bound library, with the matching bound and the relCost corollary, was tested the same way in job 2021637 on a Linux x86_64 cluster node with 8 cores, from a fresh copy of this repository's files with elan, Lean 4.35.0 and the caches installed fresh. It started on 2026-11-25 (US Pacific time) and ran for 12 minutes 25 seconds. `lake exe cache get` took 207 seconds. `lake build LowerBounds` took 399 seconds, which includes compiling the needed parts of Google's library, and built all 17 modules without errors and without `sorry` (with deprecation and linter warnings). `lake env lean checks/GroverAxioms.lean` took 41 seconds. Besides the printed definitions, it reported

```
GroverThreeFifths.findAny_lower_bound_35 : GroverLowerBound.FindAnyLowerBound (3 / 5) 16
'GroverThreeFifths.findAny_lower_bound_35' depends on axioms: [propext, Classical.choice, Quot.sound]
'GroverLowerBound.findAny_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
def GroverThreeFifths.FullConstantTarget : Prop :=
GroverThreeFifths.FindAnyLowerBoundErr (Real.pi / 8 + 1 / 4) (fun n => 4 / √(2 ^ n)) 2
GroverThreeFifths.findAny_lower_bound_full : GroverThreeFifths.FullConstantTarget
'GroverThreeFifths.findAny_lower_bound_full' depends on axioms: [propext, Classical.choice, Quot.sound]
def GroverThreeFifths.RelCostFloor11 : Prop :=
∀ (F : GroverThreeFifths.FindAnyFiller),
  GroverThreeFifths.SolvesFindAny F → F.cells 1 1 = true → 12 / (5 * Real.pi) < ↑(F.relCost 1 1)
GroverThreeFifths.relCost_floor_11 : GroverThreeFifths.RelCostFloor11
'GroverThreeFifths.relCost_floor_11' depends on axioms: [propext, Classical.choice, Quot.sound]
```

In the same job, a separate file outside this repository checked that Google's own `groverFindAny_correctness` and `groverFindAny_rel_cost` type-check as a proof of `SolvesFindAny` for Google's holes, so for Google's holes the restatement in `SolvesFindAny` is the two challenge theorems as compiled from Google's specification.

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

This work builds on Google DeepMind's [formal-quantum-computation](https://github.com/google-deepmind/formal-quantum-computation), released under the Apache License 2.0 and described in S. Shirobokov et al., "Discovering formally verified quantum programs with AI", [arXiv:2611.09822](https://arxiv.org/abs/2611.09822) (2026). The specification format, the circuit and resource-counting framework, the correctness predicates and the Comparator workflow are theirs. Nine solution files contain sections copied from the `discoveries` branch of that repository, marked `GOOGLE-DERIVED`; each names Google LLC in its header and states its modifications, and `NOTICE` lists them. `LowerBounds/Grover/Statement.lean` restates three definitions from Google's Grover specification in the same way, and `LowerBounds/Grover/RelCostStatement.lean` restates the challenge's hole types, its program construction and the statements of two of its theorems. This repository is not affiliated with or endorsed by Google DeepMind.

Copyright 2026 Marlon Moenius. Licensed under the Apache License, Version 2.0; see `LICENSE`.
