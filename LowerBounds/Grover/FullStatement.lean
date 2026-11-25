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
import LowerBounds.Grover.Statement

/-!
# Lower-bound statement with an error term

`FindAnyLowerBoundErr C E n₀` is `GroverLowerBound.FindAnyLowerBound` (`Statement.lean`) with the
conclusion `C * √(2 ^ n) ≤ bound` replaced by `C * √(2 ^ n) - E n ≤ bound`. Binders, the circuit
type, `MeetsFindAnySpec` and the `AvgOracleCostBound` hypothesis are the same.

`FullConstantTarget` instantiates it with `C = π / 8 + 1 / 4`, `E n = 4 / √(2 ^ n)` and `n₀ = 2`.
This file proves nothing; `FullBound.lean` proves `FullConstantTarget`.
-/

namespace GroverThreeFifths

open QuantumComputation.Specs Operator ResourceCounting Real
open QuantumComputation.Specs.Grover (Var)
open GroverLowerBound

/-- Every circuit that meets the find-any spec at `m = k = 1` has uniform-average expected oracle
rounds at least `C * √(2 ^ n) - E n`, for all `n ≥ n₀`. -/
def FindAnyLowerBoundErr (C : ℝ) (E : ℕ → ℝ) (n₀ : ℕ) : Prop :=
  ∀ n ≥ n₀, ∀ (Q : ℕ) (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1)),
    MeetsFindAnySpec c →
    ∀ bound : ℝ,
      AvgOracleCostBound 1
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle 1 S))
        (fun S ↦ findAnyProgramOf c S) bound →
      C * √((2 : ℝ) ^ n) - E n ≤ bound

/-- The constant `π/8 + 1/4` of Google's verified solution, with error `4 / √(2 ^ n)`, for
every `n ≥ 2` (`N ≥ 4`). -/
def FullConstantTarget : Prop :=
  FindAnyLowerBoundErr (π / 8 + 1 / 4) (fun n ↦ 4 / √((2 : ℝ) ^ n)) 2

end GroverThreeFifths
