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
import QuantumComputationSpecs.Algorithms.Grover

/-!
# Shared definitions for the find-any lower bounds

* `LF`: loop-free oracle circuits with `abort`, and `LF.compile` into the library's `QProg`.
* `unroll N`: replaces every `qWhile` of an `OracleDynamicCircuit` by its `N`-fold unrolling
  (the library's `whileRec`, as syntax).
* `Branch`, `ens`: a finite list of classical branches. A branch carries its store, the number of
  oracle nodes it has passed, a `live` flag (cleared by `abort`; dead branches are kept and never
  change) and one unnormalised state vector for each run index `i : ι`. All runs share the
  branching structure; they differ only in the matrix `G i k r` applied at an oracle node on
  register `r` by a branch that has passed `k` oracle nodes.
-/

open QuantumComputation.Specs Operator
open scoped Matrix

namespace GroverLowerBound

/-- Loop-free oracle circuits on `Q` qubits with an oracle of width `w`, with `abort`. -/
inductive LF (Var : Type) (Q w : ℕ) : Type where
  | skip : LF Var Q w
  | abort : LF Var Q w
  | step : Unitary (2 ^ Q) → LF Var Q w
  | oracle : QRegister w Q → LF Var Q w
  | measure {k : ℕ} : Var → QRegister k Q → LF Var Q w
  | qIf (b : Store Var → Prop) [DecidablePred b] : LF Var Q w → LF Var Q w → LF Var Q w
  | seq : LF Var Q w → LF Var Q w → LF Var Q w

namespace LF

variable {Var : Type} {Q w : ℕ}

/-- Compilation to the library's programs: `oracle r` becomes the embedded oracle unitary. -/
noncomputable def compile (O : Unitary (2 ^ w)) : LF Var Q w → QProg Var (2 ^ Q)
  | .skip => .skip
  | .abort => .abort
  | .step U => .qAssign U
  | .oracle r => .qAssign (r.embedUnitary O)
  | .measure v r => QProg.measureRegister v r
  | @LF.qIf _ _ _ b _ t f => .qIf b (compile O t) (compile O f)
  | .seq p₁ p₂ => .qSeq (compile O p₁) (compile O p₂)

/-- The `n`-fold unrolling of a loop: the syntax of the library's `whileRec`. -/
def whileN (b : Store Var → Prop) [DecidablePred b] (body : LF Var Q w) : ℕ → LF Var Q w
  | 0 => .abort
  | n + 1 => .qIf b (.seq body (whileN b body n)) .skip

end LF

/-- Replace every loop by its `N`-fold unrolling. -/
def unroll {Var : Type} {Q w : ℕ} (N : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w → LF Var Q w
  | .skip => .skip
  | .step U => .step U
  | .oracle r => .oracle r
  | .measure v r => .measure v r
  | @OracleDynamicCircuit.qIf _ _ _ _ b _ t f => .qIf b (unroll N t) (unroll N f)
  | @OracleDynamicCircuit.qWhile _ _ _ _ b _ body => LF.whileN b (unroll N body) N
  | .seq p₁ p₂ => .seq (unroll N p₁) (unroll N p₂)

/-- One classical branch of a family of runs indexed by `ι`. -/
structure Branch (Var ι : Type) (Q : ℕ) where
  /-- classical store -/
  store : Store Var
  /-- number of oracle nodes passed -/
  count : ℕ
  /-- cleared by `abort` -/
  live : Bool
  /-- unnormalised state vector of each run -/
  vec : ι → Fin (2 ^ Q) → ℂ

section ens

variable {Var : Type} [DecidableEq Var] {ι : Type} {Q w : ℕ}

/-- Branch semantics of a loop-free circuit. `G i k r` is the matrix that run `i` applies at an
oracle node on register `r` when the branch has passed `k` oracle nodes before it. -/
noncomputable def ens (G : ι → ℕ → QRegister w Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ) :
    LF Var Q w → List (Branch Var ι Q) → List (Branch Var ι Q)
  | .skip, E => E
  | .abort, E => E.map fun β ↦ { β with live := false }
  | .step U, E => E.map fun β ↦
      if β.live then { β with vec := fun i ↦ U.1 *ᵥ β.vec i } else β
  | .oracle r, E => E.map fun β ↦
      if β.live then
        { β with count := β.count + 1, vec := fun i ↦ G i β.count r *ᵥ β.vec i }
      else β
  | @LF.measure _ _ _ k v r, E => E.flatMap fun β ↦
      if β.live then
        (List.finRange (2 ^ k)).map fun o ↦
          { β with
            store := Function.update β.store v (o.val : ℤ)
            vec := fun i ↦ (r.computationalBasisMeasurement.1 o) *ᵥ β.vec i }
      else [β]
  | @LF.qIf _ _ _ b _ t f, E =>
      ens G t (E.filter fun β ↦ decide (b β.store)) ++
        ens G f (E.filter fun β ↦ !decide (b β.store))
  | .seq p₁ p₂, E => ens G p₂ (ens G p₁ E)

end ens

/-- Squared norm of a coordinate vector. -/
noncomputable def nsq {d : ℕ} (v : Fin d → ℂ) : ℝ := ∑ j, Complex.normSq (v j)

/-- The run indices of the hybrid argument: `none` is the reference run (no oracle is ever
applied), `some (x, l)` applies the oracle of the marked item `x` at every oracle node except the
first `l` ones on each branch. So `some (x, 0)` is the real run with marked item `x`. -/
abbrev HIdx (n : ℕ) : Type := Option (Fin (2 ^ n) × ℕ)

/-- The oracle matrices of the hybrid runs. -/
noncomputable def hybridG {n Q : ℕ} :
    HIdx n → ℕ → QRegister ((n + 1) * 1) Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ
  | none, _, _ => 1
  | some (x, l), k, r =>
      if l ≤ k then (r.embedUnitary (groverParallelMarkingOracle 1 {x})).1 else 1

/-- The initial branch: store `σ₀`, no oracle node passed, every run in the basis state `0`. -/
noncomputable def initBranch {Var ι : Type} {Q : ℕ} (σ₀ : Store Var) : Branch Var ι Q where
  store := σ₀
  count := 0
  live := true
  vec := fun _ ↦ Pi.single 0 1

end GroverLowerBound
