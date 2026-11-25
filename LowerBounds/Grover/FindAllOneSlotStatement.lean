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
import LowerBounds.Grover.ParallelRelCostStatement

/-!
# The one-slot find-all relCost floor, stated against the challenge's holes

`RelCostFloorAllB`: every filler that solves find-all (`SolvesFindAll`,
`ParallelRelCostStatement.lean`) and claims a cell `(1, k)` with `k ≥ 1` has
`2 / π < relCost 1 k`. This file states the floor; `FindAllOneSlot.lean` proves it.
-/

namespace GroverParallel

open Real

/-- The find-all floor at m = 1: no solution of the find-all challenge that claims cell `(1, k)`
can certify a relCost at or below `2/π`. -/
def RelCostFloorAllB : Prop :=
  ∀ F : FindAllFiller, SolvesFindAll F → ∀ k : ℕ, 1 ≤ k → F.cells 1 k = true →
    (2 / π : ℝ) < (F.relCost 1 k : ℝ)

end GroverParallel
