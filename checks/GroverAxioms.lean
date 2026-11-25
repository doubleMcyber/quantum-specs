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
import LowerBounds.Grover.ThreeFifthsBound
import LowerBounds.Grover.FullBound
import LowerBounds.Grover.RelCost

/-!
Prints the statement and the axioms of the Grover find-any lower bounds. Run after
`lake build LowerBounds` with

    lake env lean checks/GroverAxioms.lean

The expected axioms are `propext`, `Classical.choice` and `Quot.sound`, and no `sorryAx`.
-/

#print GroverLowerBound.FindAnyLowerBound
#check @GroverThreeFifths.findAny_lower_bound_35
#print axioms GroverThreeFifths.findAny_lower_bound_35
#print axioms GroverLowerBound.findAny_lower_bound

#print GroverThreeFifths.FindAnyLowerBoundErr
#print GroverThreeFifths.FullConstantTarget
#check @GroverThreeFifths.findAny_lower_bound_full
#print axioms GroverThreeFifths.findAny_lower_bound_full

#print GroverThreeFifths.SolvesFindAny
#print GroverThreeFifths.RelCostFloor11
#check @GroverThreeFifths.relCost_floor_11
#print axioms GroverThreeFifths.relCost_floor_11
