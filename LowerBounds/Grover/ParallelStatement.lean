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
# Lower-bound statements for Grover find-any and find-all at every cell `(m, k)`

`FindAnyLowerBoundMK m k C n₀` extends `GroverLowerBound.FindAnyLowerBound` (`Statement.lean`) from
`m = k = 1` to any number `m` of oracle slots per round and any number `k` of marked items. It is
written against the unmodified definitions of `QuantumComputationSpecs.Algorithms.Grover` in Google
DeepMind's formal-quantum-computation. It says: for every `n ≥ n₀`, every oracle circuit on any
number of qubits whose program, built as the specification builds `groverFindAnyProgram`, meets
`groverFindAny_correctness` at cell `(m, k)` (for every marked set `S` in
`groverTargetSets n k`, the register `res` ends holding an element of `S`), and every bound accepted
by `AvgOracleCostBound` for that program under `CostModel.ofEmbeddedOracle`, satisfies
`C * √(2 ^ n / (m k)) ≤ bound`. `FindAllLowerBoundMK` is the same with the postcondition of
`groverFindAll_correctness` (`decodeTargets n k` of `res` is `S`).

This file states the bounds and proves nothing. `ParallelBound.lean` proves both with `C = 3 / 5`
and `n₀ = n0_of m k = 16 + Nat.clog 2 (m * k)`, for all `m, k ≥ 1`. `ParallelFullStatement.lean`
states them with an error term.

The definitions between the GOOGLE-DERIVED markers restate the program construction shared by
`groverFindAnyProgram` and `groverFindAllProgram`, the postconditions of
`groverFindAny_correctness` and `groverFindAll_correctness` and the cost predicate of the two
`rel_cost` theorems from `QuantumComputationSpecs/Algorithms/Grover.lean` (Copyright 2026 Google
LLC, Apache License 2.0), with the circuit and the qubit count quantified instead of fixed.
-/

namespace GroverParallel

open QuantumComputation.Specs Operator ResourceCounting Real
open QuantumComputation.Specs.Grover (Var)
open QuantumComputation.Specs.Grover.Var (res)

-- BEGIN GOOGLE-DERIVED
/-- The program the spec builds from a circuit, for an arbitrary circuit on `Q` qubits with `m`
oracle slots per round (find-any and find-all share this shape; only `Q` and the postcondition
differ). -/
noncomputable def programOf {n m Q : ℕ}
    (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m))
    (S : Finset (Fin (2 ^ n))) : QProg Var (2 ^ Q) :=
  .qSeq .qSet (c.compile QProg.qAssign (groverParallelMarkingOracle m S))

/-- `c` meets `groverFindAny_correctness` at cell `(m, k)`. -/
def MeetsFindAnySpec {n m Q : ℕ} (k : ℕ)
    (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)) : Prop :=
  ∀ S ∈ groverTargetSets n k,
    ⦃ ⊤ ⦄ programOf c S ⦃ fun σ ↦ ⌜∃ x ∈ S, σ res = x.val⌝ ⦄

/-- `c` meets `groverFindAll_correctness` at cell `(m, k)`. -/
def MeetsFindAllSpec {n m Q : ℕ} (k : ℕ)
    (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)) : Prop :=
  ∀ S ∈ groverTargetSets n k,
    ⦃ ⊤ ⦄ programOf c S ⦃ fun σ ↦ ⌜decodeTargets n k (σ res) = S⌝ ⦄

/-- Every circuit meeting the find-any spec at cell `(m, k)` has uniform-average expected oracle
rounds at least `C * √(2^n / (m k))`, for all `n ≥ n₀`. Vanilla Grover costs `(π/4)` times this. -/
def FindAnyLowerBoundMK (m k : ℕ) (C : ℝ) (n₀ : ℕ) : Prop :=
  ∀ n ≥ n₀, ∀ (Q : ℕ) (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)),
    MeetsFindAnySpec k c →
    ∀ bound : ℝ,
      AvgOracleCostBound k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦ programOf c S) bound →
      C * √((2 : ℝ) ^ n / ((m : ℝ) * k)) ≤ bound

/-- The find-all analogue. Same constant and shape; for `k > 1` the provable constant is the
find-any one (a sharper find-all constant is open). -/
def FindAllLowerBoundMK (m k : ℕ) (C : ℝ) (n₀ : ℕ) : Prop :=
  ∀ n ≥ n₀, ∀ (Q : ℕ) (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)),
    MeetsFindAllSpec k c →
    ∀ bound : ℝ,
      AvgOracleCostBound k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦ programOf c S) bound →
      C * √((2 : ℝ) ^ n / ((m : ℝ) * k)) ≤ bound
-- END GOOGLE-DERIVED

/-- The threshold used with the constant `3 / 5`. -/
def n0_of (m k : ℕ) : ℕ := 16 + Nat.clog 2 (m * k)

/-- What the threshold buys: `2^n ≥ 2^16 * m * k` for every `n ≥ n0_of m k`. -/
lemma two_pow_n0_ge (m k n : ℕ) (hn : n0_of m k ≤ n) : 2 ^ 16 * (m * k) ≤ 2 ^ n := by
  have h1 : m * k ≤ 2 ^ Nat.clog 2 (m * k) := Nat.le_pow_clog (by norm_num) _
  have h2 : 2 ^ (16 + Nat.clog 2 (m * k)) ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by norm_num) hn
  calc 2 ^ 16 * (m * k) ≤ 2 ^ 16 * 2 ^ Nat.clog 2 (m * k) := Nat.mul_le_mul_left _ h1
    _ = 2 ^ (16 + Nat.clog 2 (m * k)) := (pow_add 2 16 _).symm
    _ ≤ 2 ^ n := h2

/-- Sanity links to the spec: a solution of the frozen spec that claims cell `(m, k)` is an
instance of the quantified circuit. -/
example (n m k : ℕ) (S : Finset (Fin (2 ^ n))) :
    groverFindAnyProgram n m k (groverParallelMarkingOracle m S) =
      programOf (groverFindAnyCircuit n m k) S := rfl

example (n m k : ℕ) (S : Finset (Fin (2 ^ n))) :
    groverFindAllProgram n m k (groverParallelMarkingOracle m S) =
      programOf (groverFindAllCircuit n m k) S := rfl

/-- A type check only: the statement elaborates at m = k = 1, where it has the shape of
`GroverLowerBound.FindAnyLowerBound` up to `1 * 1` casts. -/
example : FindAnyLowerBoundMK 1 1 (3 / 5) 16 → True := fun _ ↦ trivial

end GroverParallel
