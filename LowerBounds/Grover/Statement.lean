/-
Copyright 2026 Marlon Moenius
Portions Copyright 2026 Google LLC (marked GOOGLE-DERIVED below)

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
import QuantumComputationSpecs.Algorithms.Grover

/-!
# Lower-bound statement for Grover find-any at `m = k = 1`

`FindAnyLowerBound C n₀` is written against the unmodified definitions of
`QuantumComputationSpecs.Algorithms.Grover` in Google DeepMind's formal-quantum-computation. It
says: for every `n ≥ n₀`, every oracle circuit on any number of qubits whose program, built as the
specification builds `groverFindAnyProgram`, meets `groverFindAny_correctness` at `m = k = 1` (the
marked item is in `res` with probability one, from every input state), and every bound accepted by
`AvgOracleCostBound` for that program under `CostModel.ofEmbeddedOracle`, satisfies
`C * √(2 ^ n) ≤ bound`.

This file states the bound and proves nothing. `EighthBound.lean` proves it with `C = 1 / 8`,
`n₀ = 5`; `ThreeFifthsBound.lean` proves it with `C = 3 / 5`, `n₀ = 16`.

The three definitions between the GOOGLE-DERIVED markers restate, at `m = k = 1`, the program
construction of `groverFindAnyProgram`, the postcondition of `groverFindAny_correctness` and the
cost predicate of `groverFindAny_rel_cost` from `QuantumComputationSpecs/Algorithms/Grover.lean`
(Copyright 2026 Google LLC, Apache License 2.0), with the circuit and the qubit count quantified
instead of fixed.
-/

namespace GroverLowerBound

open QuantumComputation.Specs Operator ResourceCounting Real
open QuantumComputation.Specs.Grover (Var)
open QuantumComputation.Specs.Grover.Var (res)

-- BEGIN GOOGLE-DERIVED
/-- The program the spec builds from a circuit (`groverFindAnyProgram`), for an arbitrary circuit
on `Q` qubits with one oracle slot per round. -/
noncomputable def findAnyProgramOf {n Q : ℕ}
    (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1))
    (S : Finset (Fin (2 ^ n))) : QProg Var (2 ^ Q) :=
  .qSeq .qSet (c.compile QProg.qAssign (groverParallelMarkingOracle 1 S))

/-- `c` meets `groverFindAny_correctness` at `m = k = 1`: for every one-element marked set the
program ends with the marked item in `res` with probability one. -/
def MeetsFindAnySpec {n Q : ℕ}
    (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1)) : Prop :=
  ∀ S ∈ groverTargetSets n 1,
    ⦃ ⊤ ⦄ findAnyProgramOf c S ⦃ fun σ ↦ ⌜∃ x ∈ S, σ res = x.val⌝ ⦄

/-- Every circuit that meets the find-any spec at `m = k = 1` has uniform-average expected oracle
rounds at least `C * √(2 ^ n)`, for all `n ≥ n₀`. Gemini's solution has leading constant
`π / 8 + 1 / 4`. -/
def FindAnyLowerBound (C : ℝ) (n₀ : ℕ) : Prop :=
  ∀ n ≥ n₀, ∀ (Q : ℕ) (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1)),
    MeetsFindAnySpec c →
    ∀ bound : ℝ,
      AvgOracleCostBound 1
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle 1 S))
        (fun S ↦ findAnyProgramOf c S) bound →
      C * √((2 : ℝ) ^ n) ≤ bound
-- END GOOGLE-DERIVED

/-- Sanity link to the spec: a solution of the frozen spec that claims the cell `(1, 1)` is an
instance of the quantified circuit, so `FindAnyLowerBound C n₀` bounds its certified constant. -/
example (n : ℕ) (S : Finset (Fin (2 ^ n))) :
    groverFindAnyProgram n 1 1 (groverParallelMarkingOracle 1 S) =
      findAnyProgramOf (groverFindAnyCircuit n 1 1) S := rfl

end GroverLowerBound
