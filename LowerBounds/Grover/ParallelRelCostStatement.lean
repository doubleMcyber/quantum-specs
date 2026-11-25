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
# The relCost floors at every cell, stated against the challenges' holes

Google's find-any and find-all challenges (`QuantumComputationSpecs/Algorithms/Grover.lean`) each
leave four definitions open: cells, qubits, circuit and the cost hole (`groverFindAnyCells`,
`groverFindAnyQubits`, `groverFindAnyCircuit`, `groverFindAnyRelCost`, and the `groverFindAll*`
analogues). A solution fills them and proves the correctness and `rel_cost` theorems. This file
turns the holes into the fields of `FindAnyFiller` and `FindAllFiller` and restates the two theorems
of each challenge with every hole replaced by the corresponding field (`SolvesFindAny`,
`SolvesFindAll`). The two cell-bookkeeping theorems of each challenge are not assumed, which makes
the floors stronger. The code of `FindAnyFiller`, `FindAnyFiller.program` and `SolvesFindAny` is that
of the declarations of the same names in `RelCostStatement.lean`, in this namespace.

* `RelCostFloorAny`: every filler that solves find-any and claims a cell `(m, k)` with `m, k ≥ 1`
  has `1 / 2 + 1 / π < relCost m k`.
* `RelCostFloorAll`: every filler that solves find-all and claims a cell `(m, k)` with `m, k ≥ 1`
  satisfies `(π / 8 + 1 / 4) √(2 ^ n / (m k)) ≤ relCost m k * vanillaFindAllCost n m k` for every
  `n`.

The declarations between the GOOGLE-DERIVED markers restate the hole types, the program
construction of `groverFindAnyProgram` and `groverFindAllProgram` and the statements of the
correctness and `rel_cost` theorems of both challenges from
`QuantumComputationSpecs/Algorithms/Grover.lean` (Copyright 2026 Google LLC, Apache License 2.0).
The examples at the end check, for Google's own holes put into a filler, that the filler's program
is `groverFindAnyProgram` (respectively `groverFindAllProgram`) by `rfl`, that `SolvesFindAny` and
`SolvesFindAll` unfold to the restated theorems by `Iff.rfl`, and that the challenge theorems
`groverFindAny_correctness`, `groverFindAny_rel_cost`, `groverFindAll_correctness` and
`groverFindAll_rel_cost`, at their own types, prove `SolvesFindAny` and `SolvesFindAll`. They
elaborate against the specification's open holes. This file imports only the specification and does
not prove the floors; `ParallelRelCost.lean` proves both.
-/

namespace GroverParallel

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

/-- `F` proves the two theorems of the find-any challenge that involve the program: the statements
of `groverFindAny_correctness` and `groverFindAny_rel_cost`, verbatim, with every hole replaced by
the corresponding field of `F`. -/
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

/-- The four definition holes of Google's find-all challenge, as data. -/
structure FindAllFiller where
  /-- fills `groverFindAllCells` -/
  cells : ℕ → ℕ → Bool
  /-- fills `groverFindAllQubits` -/
  qubits : ℕ → ℕ → ℕ → ℕ
  /-- fills `groverFindAllCircuit` -/
  circuit : ∀ n m k : ℕ,
    OracleDynamicCircuit (Unitary (2 ^ qubits n m k)) Var (qubits n m k) ((n + 1) * m)
  /-- fills the cost hole `groverFindAllRelCost` -/
  relCost : ℕ → ℕ → ℚ≥0

open QProg.Notation in
/-- `groverFindAllProgram` with the circuit hole filled by `F`: reset all qubits, then run the
circuit compiled with `oracle`. -/
noncomputable def FindAllFiller.program (F : FindAllFiller) (n m k : ℕ)
    (oracle : Unitary (2 ^ ((n + 1) * m))) : QProg Var (2 ^ F.qubits n m k) :=
  qset ;; (F.circuit n m k).compile QProg.qAssign oracle

/-- `F` proves the two theorems of the find-all challenge that involve the program: the statements
of `groverFindAll_correctness` and `groverFindAll_rel_cost`, verbatim, with every hole replaced by
the corresponding field of `F`. -/
def SolvesFindAll (F : FindAllFiller) : Prop :=
  (∀ {n m k : ℕ} (_hn : 1 ≤ n) (_hmk : F.cells m k = true) (_hkN : k ≤ 2 ^ n)
      {S : Finset (Fin (2 ^ n))} (_hS : S ∈ groverTargetSets n k),
      ⦃ ⊤ ⦄
      F.program n m k (groverParallelMarkingOracle m S)
      ⦃ fun σ ↦ ⌜decodeTargets n k (σ res) = S⌝ ⦄) ∧
  (∀ {m k : ℕ} (_hmk : F.cells m k = true),
      ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
        AvgOracleCostBound k
          (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
          (fun S ↦ F.program n m k (groverParallelMarkingOracle m S))
          (F.relCost m k * vanillaFindAllCost n m k))
-- END GOOGLE-DERIVED

/-- The floor for find-any at every cell: no solution of the challenge that claims cell `(m, k)`
can certify a relCost at or below `1/2 + 1/π ≈ 0.81831`. -/
def RelCostFloorAny : Prop :=
  ∀ F : FindAnyFiller, SolvesFindAny F → ∀ m k : ℕ, 1 ≤ m → 1 ≤ k → F.cells m k = true →
    (1 / 2 + 1 / π : ℝ) < (F.relCost m k : ℝ)

/-- The floor for find-all at every cell: a solution that claims cell `(m, k)` has
`(π/8 + 1/4) √(2^n / (m k)) ≤ relCost m k * vanillaFindAllCost n m k` for every `n`. -/
def RelCostFloorAll : Prop :=
  ∀ F : FindAllFiller, SolvesFindAll F → ∀ m k : ℕ, 1 ≤ m → 1 ≤ k → F.cells m k = true →
    ∀ n : ℕ, (π / 8 + 1 / 4) * √((2 : ℝ) ^ n / ((m : ℝ) * k)) ≤
      (F.relCost m k : ℝ) * vanillaFindAllCost n m k

/-- Sanity links (find-any): Google's own holes form a filler whose program is
`groverFindAnyProgram` definitionally, so `SolvesFindAny` of it is exactly the conjunction of the two
challenge theorems `groverFindAny_correctness` and `groverFindAny_rel_cost`. These elaborate against
the spec's `sorry` holes. -/
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

/-- The same sanity links for find-all. -/
example (n m k : ℕ) (oracle : Unitary (2 ^ ((n + 1) * m))) :
    (FindAllFiller.mk groverFindAllCells groverFindAllQubits groverFindAllCircuit
        groverFindAllRelCost).program n m k oracle =
      groverFindAllProgram n m k oracle := rfl

-- BEGIN GOOGLE-DERIVED
example :
    SolvesFindAll (FindAllFiller.mk groverFindAllCells groverFindAllQubits groverFindAllCircuit
        groverFindAllRelCost) ↔
      ((∀ {n m k : ℕ} (_hn : 1 ≤ n) (_hmk : groverFindAllCells m k = true) (_hkN : k ≤ 2 ^ n)
          {S : Finset (Fin (2 ^ n))} (_hS : S ∈ groverTargetSets n k),
          ⦃ ⊤ ⦄
          groverFindAllProgram n m k (groverParallelMarkingOracle m S)
          ⦃ fun σ ↦ ⌜decodeTargets n k (σ res) = S⌝ ⦄) ∧
       (∀ {m k : ℕ} (_hmk : groverFindAllCells m k = true),
          ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
            AvgOracleCostBound k
              (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
              (fun S ↦ groverFindAllProgram n m k (groverParallelMarkingOracle m S))
              (groverFindAllRelCost m k * vanillaFindAllCost n m k))) := Iff.rfl
-- END GOOGLE-DERIVED

/-- The challenge theorems themselves, at their own types, prove `SolvesFindAny` and
`SolvesFindAll` of Google's holes, so the hand-typed right-hand sides above cannot drift from
the specification unnoticed. -/
example : SolvesFindAny (FindAnyFiller.mk groverFindAnyCells groverFindAnyQubits groverFindAnyCircuit
    groverFindAnyRelCost) :=
  ⟨@groverFindAny_correctness, @groverFindAny_rel_cost⟩

example : SolvesFindAll (FindAllFiller.mk groverFindAllCells groverFindAllQubits groverFindAllCircuit
    groverFindAllRelCost) :=
  ⟨@groverFindAll_correctness, @groverFindAll_rel_cost⟩

end GroverParallel
