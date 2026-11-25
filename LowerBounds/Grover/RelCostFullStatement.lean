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
import LowerBounds.Grover.RelCostStatement

/-!
# The sharp relCost floor at cell (1, 1), statement

`RelCostFloor11Full` says that every filler of the four holes of Google's find-any challenge that
proves `groverFindAny_correctness` and `groverFindAny_rel_cost` (`SolvesFindAny`,
`RelCostStatement.lean`) and claims cell (1, 1) has `1 / 2 + 1 / π < relCost 1 1`.

This file proves nothing; `RelCostFull.lean` proves `RelCostFloor11Full`.
-/

namespace GroverThreeFifths

open Real

/-- The sharp floor at cell (1, 1). -/
def RelCostFloor11Full : Prop :=
  ∀ F : FindAnyFiller, SolvesFindAny F → F.cells 1 1 = true →
    (1 / 2 + 1 / π : ℝ) < (F.relCost 1 1 : ℝ)

end GroverThreeFifths
