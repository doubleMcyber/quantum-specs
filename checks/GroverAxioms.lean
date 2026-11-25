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
import LowerBounds.Grover.RelCostFull
import LowerBounds.Grover.ParallelBound

/-!
Prints the statements and the axioms of the Grover lower bounds (find-any at cell (1, 1), find-any
and find-all at every cell `(m, k)`, and the relCost floors at cell (1, 1)). Run after
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
#print GroverThreeFifths.RelCostFloor11Full
#check @GroverThreeFifths.relCost_floor_11_full
#print axioms GroverThreeFifths.relCost_floor_11_full

#print GroverParallel.FindAnyLowerBoundMK
#print GroverParallel.FindAllLowerBoundMK
#print GroverParallel.FindAnyLowerBoundMKErr
#print GroverParallel.FindAllLowerBoundMKErr
#print GroverParallel.FullTargetAny
#print GroverParallel.FullTargetAll
#check @GroverParallel.fullTargetAny
#print axioms GroverParallel.fullTargetAny
#check @GroverParallel.fullTargetAll
#print axioms GroverParallel.fullTargetAll
#check @GroverParallel.findAny_35
#print axioms GroverParallel.findAny_35
#check @GroverParallel.findAll_35
#print axioms GroverParallel.findAll_35
