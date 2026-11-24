# Quantum primitive specifications for formal-quantum-computation

This repository contains frozen Lean 4 specifications of quantum arithmetic, table lookup, modular arithmetic, prime-field and elliptic-curve arithmetic, block-encoding and estimation primitives. They are written in the format of Google DeepMind's [formal-quantum-computation](https://github.com/google-deepmind/formal-quantum-computation) library. Seventeen of the nineteen specifications come with a baseline solution whose correctness and cost are proved in Lean. With two extra elliptic-curve solutions and an alias-sampling PREPARE solution there are twenty solution modules, and the Comparator has accepted all twenty.

The specifications and proofs were written with AI coding agents. Lean's kernel and the Comparator checked them.

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

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain (Lean v4.35.0) is pinned in `lean-toolchain`. Then:

```bash
git clone <this repository>
cd <this repository>
lake exe cache get                       # downloads Mathlib's prebuilt files
lake build                               # builds every specification
lake build QuantumSolutions              # builds every solution
lake build QuantumSolutions.Arithmetic.Adder   # builds one solution
```

Google's library has no prebuilt cache, so the first build compiles its modules from source.

To check a solution with the Comparator, on Linux with [bubblewrap](https://github.com/containers/bubblewrap) installed:

```bash
lake comparator --config comparator/Adder.json
```

The run passes when it prints `Your solution is okay!`. The sandbox needs bubblewrap, which exists only on Linux. On macOS the Comparator runs only unsandboxed, with `lake comparator --inadvisably-no-sandbox --config comparator/Adder.json`; an unsandboxed run trusts the solution's build not to tamper with the check.

These steps were tested on 2026-11-24 on a Linux x86_64 cluster node, starting from a fresh copy of this repository's files, with elan and Lean 4.35.0 installed fresh and empty Lake and Mathlib caches. `lake exe cache get` fetched every dependency from GitHub at the revisions in `lake-manifest.json` and downloaded Mathlib's prebuilt files (about 2 minutes). `lake build` built the 19 specifications (about 2 minutes) and `lake build QuantumSolutions` built the 20 solutions (about 5 minutes on 8 cores). The sandboxed Comparator then passed on five configurations, each in about 2 minutes: PreparePauliLCUAlias, Adder, TableLookup, SelectPauli and ECPointAddProjPoly. The other fifteen configurations were not rerun from this fresh copy.

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

## Submitting a better solution

1. Copy the baseline module, for example `QuantumSolutions/Arithmetic/Adder.lean`, to a new module such as `QuantumSolutions/Arithmetic/AdderYourName.lean`. A solution restates the whole specification in the namespace `QuantumComputation.Specs`, fills the holes and proves the frozen theorems. It does not import the specification module. Leave every declaration that is not a hole exactly as it is: the Comparator compares the compiled declarations, including their reducibility, which is why frozen helper definitions that mention a hole are `abbrev`s.
2. Fill the holes with your construction and a smaller cost. Make the program a computable definition and each cost hole a closed number, provable by `rfl` or `decide` at the pinned sizes, so that the result is a circuit and a number rather than an existence proof.
3. Copy `comparator/Adder.json` to `comparator/AdderYourName.json` and set `solution_module` to your module.
4. Run `lake build QuantumSolutions.Arithmetic.AdderYourName` and `lake comparator --config comparator/AdderYourName.json` on Linux, so that the run is sandboxed.
5. Open a pull request with the module, the configuration and the full Comparator output.

A change to a specification's statement is a new specification and needs a new baseline proof.

## Credits and licence

This work builds on Google DeepMind's [formal-quantum-computation](https://github.com/google-deepmind/formal-quantum-computation), released under the Apache License 2.0 and described in S. Shirobokov et al., "Discovering formally verified quantum programs with AI", [arXiv:2611.09822](https://arxiv.org/abs/2611.09822) (2026). The specification format, the circuit and resource-counting framework, the correctness predicates and the Comparator workflow are theirs. Nine solution files contain sections copied from the `discoveries` branch of that repository, marked `GOOGLE-DERIVED`; each names Google LLC in its header and states its modifications, and `NOTICE` lists them. This repository is not affiliated with or endorsed by Google DeepMind.

Copyright 2026 Marlon Moenius. Licensed under the Apache License, Version 2.0; see `LICENSE`.
