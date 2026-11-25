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
# The relCost floor at cell (1, 1), stated against the challenge's holes

Google's find-any challenge (`QuantumComputationSpecs/Algorithms/Grover.lean`) leaves four
definitions open: `groverFindAnyCells`, `groverFindAnyQubits`, `groverFindAnyCircuit` and the cost
hole `groverFindAnyRelCost`. A solution fills them and proves `groverFindAny_correctness` and
`groverFindAny_rel_cost`. This file turns the holes into the fields of `FindAnyFiller` and restates
the two theorems with the holes replaced by those fields (`SolvesFindAny`). `RelCostFloor11` says
that every filler that proves both and claims cell (1, 1) has `12 / (5 π) < relCost 1 1`.

The declarations between the GOOGLE-DERIVED markers restate the hole types, the program
construction of `groverFindAnyProgram` and the statements of `groverFindAny_correctness` and
`groverFindAny_rel_cost` from `QuantumComputationSpecs/Algorithms/Grover.lean` (Copyright 2026
Google LLC, Apache License 2.0). This file imports only the specification and proves nothing;
`RelCost.lean` proves `RelCostFloor11`.
-/

namespace GroverThreeFifths

open QuantumComputation.Specs Operator ResourceCounting Real
open QuantumComputation.Specs.Grover (Var)
open QuantumComputation.Specs.Grover.Var (res)
open scoped NNReal NNRat

-- BEGIN GOOGLE-DERIVED
/-- The four definition holes of Google's find-any challenge, as data. -/
structure FindAnyFiller where
  /-- fills `groverFindAnyCells` -/
  cells : ℕ → ℕ → Bool
  /-- fills `groverFindAnyQubits` -/
  qubits : ℕ → ℕ → ℕ → ℕ
  /-- fills `groverFindAnyCircuit` -/
  circuit : ∀ n m k : ℕ,
    OracleDynamicCircuit (Unitary (2 ^ qubits n m k)) Var (qubits n m k) ((n + 1) * m)
  /-- fills the cost hole `groverFindAnyRelCost` -/
  relCost : ℕ → ℕ → ℚ≥0

open QProg.Notation in
/-- `groverFindAnyProgram` with the circuit hole filled by `F`: reset all qubits, then run the
circuit compiled with `oracle`. -/
noncomputable def FindAnyFiller.program (F : FindAnyFiller) (n m k : ℕ)
    (oracle : Unitary (2 ^ ((n + 1) * m))) : QProg Var (2 ^ F.qubits n m k) :=
  qset ;; (F.circuit n m k).compile QProg.qAssign oracle

/-- `F` proves the two theorems of the challenge that involve the program: the statements of
`groverFindAny_correctness` and `groverFindAny_rel_cost`, verbatim, with every hole replaced by the
corresponding field of `F`. (The two cell-bookkeeping theorems `groverFindAnyCells_nonempty` and
`groverFindAnyCells_mem_grid` are not assumed; leaving them out makes the floor stronger.) -/
def SolvesFindAny (F : FindAnyFiller) : Prop :=
  (∀ {n m k : ℕ} (_hn : 1 ≤ n) (_hmk : F.cells m k = true) (_hkN : k ≤ 2 ^ n)
      {S : Finset (Fin (2 ^ n))} (_hS : S ∈ groverTargetSets n k),
      ⦃ ⊤ ⦄
      F.program n m k (groverParallelMarkingOracle m S)
      ⦃ fun σ ↦ ⌜∃ x ∈ S, σ res = x.val⌝ ⦄) ∧
  (∀ {m k : ℕ} (_hmk : F.cells m k = true),
      ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
        AvgOracleCostBound k
          (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
          (fun S ↦ F.program n m k (groverParallelMarkingOracle m S))
          (F.relCost m k * vanillaFindAnyCost n m k))
-- END GOOGLE-DERIVED

/-- The floor at cell (1, 1): no solution of the challenge that claims cell (1, 1) can certify a
relCost at or below `12 / (5 π) ≈ 0.76394`. (Google's verified solution certifies about `0.81831`.) -/
def RelCostFloor11 : Prop :=
  ∀ F : FindAnyFiller, SolvesFindAny F → F.cells 1 1 = true →
    (12 / (5 * π) : ℝ) < (F.relCost 1 1 : ℝ)

/-- Sanity link: Google's own holes form a filler whose program is `groverFindAnyProgram`
definitionally, so `SolvesFindAny` of it is exactly the conjunction of the two challenge theorems
`groverFindAny_correctness` and `groverFindAny_rel_cost`. -/
example (n m k : ℕ) (oracle : Unitary (2 ^ ((n + 1) * m))) :
    (FindAnyFiller.mk groverFindAnyCells groverFindAnyQubits groverFindAnyCircuit
        groverFindAnyRelCost).program n m k oracle =
      groverFindAnyProgram n m k oracle := rfl

-- BEGIN GOOGLE-DERIVED
example :
    SolvesFindAny (FindAnyFiller.mk groverFindAnyCells groverFindAnyQubits groverFindAnyCircuit
        groverFindAnyRelCost) ↔
      ((∀ {n m k : ℕ} (_hn : 1 ≤ n) (_hmk : groverFindAnyCells m k = true) (_hkN : k ≤ 2 ^ n)
          {S : Finset (Fin (2 ^ n))} (_hS : S ∈ groverTargetSets n k),
          ⦃ ⊤ ⦄
          groverFindAnyProgram n m k (groverParallelMarkingOracle m S)
          ⦃ fun σ ↦ ⌜∃ x ∈ S, σ res = x.val⌝ ⦄) ∧
       (∀ {m k : ℕ} (_hmk : groverFindAnyCells m k = true),
          ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
            AvgOracleCostBound k
              (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
              (fun S ↦ groverFindAnyProgram n m k (groverParallelMarkingOracle m S))
              (groverFindAnyRelCost m k * vanillaFindAnyCost n m k))) := Iff.rfl
-- END GOOGLE-DERIVED

end GroverThreeFifths
