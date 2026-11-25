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
import LowerBounds.Grover.ParallelStatement

/-!
# Lower-bound statements with an error term at every cell `(m, k)`

`FindAnyLowerBoundMKErr m k C E n₀` is `FindAnyLowerBoundMK` (`ParallelStatement.lean`) with the
conclusion `C * √(2 ^ n / (m k)) ≤ bound` replaced by `C * √(2 ^ n / (m k)) - E n ≤ bound`.
`FindAllLowerBoundMKErr` does the same for find-all. Binders, the circuit type, the correctness
predicates and the `AvgOracleCostBound` hypothesis are unchanged.

`FullTargetAny m k` and `FullTargetAll m k` instantiate them with `C = π / 8 + 1 / 4`,
`E n = errMK m k n = 4 / √(2 ^ n / (m k))` and `n₀ = n0full m k = 2 + Nat.clog 2 (m * k)`, the
least `n` with `2 ^ n ≥ 4 m k`. This file proves nothing beyond that threshold arithmetic
(`two_pow_n0full_ge`); `ParallelBound.lean` proves both targets for all `m, k ≥ 1`.
-/

namespace GroverParallel

open QuantumComputation.Specs Operator ResourceCounting Real
open QuantumComputation.Specs.Grover (Var)

/-- Every circuit meeting the find-any spec at cell `(m, k)` has uniform-average expected oracle
rounds at least `C * √(2^n / (m k)) - E n`, for all `n ≥ n₀`. -/
def FindAnyLowerBoundMKErr (m k : ℕ) (C : ℝ) (E : ℕ → ℝ) (n₀ : ℕ) : Prop :=
  ∀ n ≥ n₀, ∀ (Q : ℕ) (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)),
    MeetsFindAnySpec k c →
    ∀ bound : ℝ,
      AvgOracleCostBound k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦ programOf c S) bound →
      C * √((2 : ℝ) ^ n / ((m : ℝ) * k)) - E n ≤ bound

/-- The find-all analogue (same constant; sharp only at k = 1). -/
def FindAllLowerBoundMKErr (m k : ℕ) (C : ℝ) (E : ℕ → ℝ) (n₀ : ℕ) : Prop :=
  ∀ n ≥ n₀, ∀ (Q : ℕ) (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)),
    MeetsFindAllSpec k c →
    ∀ bound : ℝ,
      AvgOracleCostBound k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦ programOf c S) bound →
      C * √((2 : ℝ) ^ n / ((m : ℝ) * k)) - E n ≤ bound

/-- The error term `4 / √(2^n / (m k))`; at m = k = 1 it is the error `4 / √(2^n)` of
`GroverThreeFifths.FullConstantTarget`. -/
noncomputable def errMK (m k n : ℕ) : ℝ := 4 / √((2 : ℝ) ^ n / ((m : ℝ) * k))

/-- Threshold for the full constant: `2^n ≥ 4 m k`, i.e. `√(2^n/(m k)) ≥ 2`. -/
def n0full (m k : ℕ) : ℕ := 2 + Nat.clog 2 (m * k)

/-- The full-constant targets at cell `(m, k)`. -/
def FullTargetAny (m k : ℕ) : Prop :=
  FindAnyLowerBoundMKErr m k (π / 8 + 1 / 4) (errMK m k) (n0full m k)
def FullTargetAll (m k : ℕ) : Prop :=
  FindAllLowerBoundMKErr m k (π / 8 + 1 / 4) (errMK m k) (n0full m k)

lemma two_pow_n0full_ge (m k n : ℕ) (hn : n0full m k ≤ n) : 4 * (m * k) ≤ 2 ^ n := by
  have h1 : m * k ≤ 2 ^ Nat.clog 2 (m * k) := Nat.le_pow_clog (by norm_num) _
  have h2 : 2 ^ (2 + Nat.clog 2 (m * k)) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  calc 4 * (m * k) ≤ 4 * 2 ^ Nat.clog 2 (m * k) := Nat.mul_le_mul_left _ h1
    _ = 2 ^ (2 + Nat.clog 2 (m * k)) := by rw [pow_add]; norm_num
    _ ≤ 2 ^ n := h2

/-- At m = k = 1 the target has the threshold and the error term of `GroverThreeFifths.FullConstantTarget`
(threshold 2, error `4/√(2^n)`). -/
example : n0full 1 1 = 2 := by decide
example (n : ℕ) : errMK 1 1 n = 4 / √((2 : ℝ) ^ n) := by simp [errMK]

end GroverParallel
