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
# The reveal find-all relCost floor, stated against the challenge's holes

`RelCostFloorAllD`: every filler that solves find-all and claims a cell `(m, k)` with `m, k ≥ 1`
has `(1 / 2 + 1 / π) / groverHarmonicSqrtSum k ≤ relCost m k`. This file states the floor;
`FindAllReveal.lean` proves it.
-/

namespace GroverParallel

open QuantumComputation.Specs Real

/-- The reveal floor: no solution of the find-all challenge that claims cell `(m, k)` can certify a
relCost below `(1/2 + 1/π) / groverHarmonicSqrtSum k`. -/
def RelCostFloorAllD : Prop :=
  ∀ F : FindAllFiller, SolvesFindAll F → ∀ m k : ℕ, 1 ≤ m → 1 ≤ k → F.cells m k = true →
    (1 / 2 + 1 / π : ℝ) / groverHarmonicSqrtSum k ≤ (F.relCost m k : ℝ)

end GroverParallel
