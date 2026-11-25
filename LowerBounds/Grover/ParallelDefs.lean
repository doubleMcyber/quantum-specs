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
import LowerBounds.Grover.Defs
import Mathlib

/-!
# Shared definitions for the lower bounds at every cell `(m, k)`

* `meanS`, `avgS`: the mean of the run vectors and their average squared norm, as `meanV` and
  `avgW` in `Mean.lean`, but over an arbitrary finite run index instead of `Fin (2 ^ n)`.
* `KSet n k`: the marked sets in `groverTargetSets n k`, as a type. It is the run index at cell
  `(m, k)`.
-/

open QuantumComputation.Specs GroverLowerBound

namespace GroverParallel

/-- Mean of the run vectors over a finite index type. -/
noncomputable def meanS {ι : Type} [Fintype ι] {Q : ℕ} (v : ι → Fin (2 ^ Q) → ℂ) :
    Fin (2 ^ Q) → ℂ :=
  fun j => ((Fintype.card ι : ℕ) : ℂ)⁻¹ * ∑ i, v i j

/-- Average squared norm of the run vectors. -/
noncomputable def avgS {ι : Type} [Fintype ι] {Q : ℕ} (v : ι → Fin (2 ^ Q) → ℂ) : ℝ :=
  ((Fintype.card ι : ℕ) : ℝ)⁻¹ * ∑ i, nsq (v i)

/-- The k-element marked sets of `Fin (2 ^ n)`, as a finite type. -/
abbrev KSet (n k : ℕ) : Type := {S : Finset (Fin (2 ^ n)) // S ∈ groverTargetSets n k}

example (n k : ℕ) : Fintype (KSet n k) := inferInstance

end GroverParallel
