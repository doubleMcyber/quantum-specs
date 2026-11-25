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
import LowerBounds.Grover.ParallelRelCost
import LowerBounds.Grover.FindAllOneSlot
import LowerBounds.Grover.FindAllSlots
import LowerBounds.Grover.FindAllReveal

/-!
Prints the statements and the axioms of the Grover lower bounds (find-any at cell (1, 1), find-any
and find-all at every cell `(m, k)`, the relCost floors at cell (1, 1), the find-any and find-all
relCost floors at every cell, and the three find-all floors: one slot, `m` slots and reveal).
Run after `lake build LowerBounds` with

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

#print GroverParallel.SolvesFindAny
#print GroverParallel.SolvesFindAll
#print GroverParallel.RelCostFloorAny
#print GroverParallel.RelCostFloorAll
#check @GroverParallel.relCost_floor_any
#print axioms GroverParallel.relCost_floor_any
#check @GroverParallel.relCost_floor_all
#print axioms GroverParallel.relCost_floor_all

#print GroverParallel.jc
#print GroverParallel.jdelta
#print GroverParallel.FL
#check @GroverParallel.findAll_floor_FL
#print axioms GroverParallel.findAll_floor_FL
#print GroverParallel.RelCostFloorAllB
#check @GroverParallel.relCost_floor_allB
#print axioms GroverParallel.relCost_floor_allB
#check @GroverParallel.findAll_floor_FL_m
#print axioms GroverParallel.findAll_floor_FL_m
#print GroverParallel.RelCostFloorAllC
#check @GroverParallel.relCost_floor_allC
#print axioms GroverParallel.relCost_floor_allC
#check @GroverParallel.findAll_floor_reveal
#print axioms GroverParallel.findAll_floor_reveal
#print GroverParallel.RelCostFloorAllD
#check @GroverParallel.relCost_floor_allD
#print axioms GroverParallel.relCost_floor_allD
