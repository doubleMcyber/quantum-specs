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
module

public import QuantumComputation.QuantumHoareLogic.ResourceCounting.CostBounds
public import QuantumComputation.Circuits.DynamicCircuit
public import QuantumComputation.Primitives.Phase
public import QuantumComputation.QuantumHoareLogic.WP

/-!
# Phase Estimation Specification

Query-model specification for estimating an unknown phase `θ ∈ ℝ` (defined modulo `1`) given
black-box access to the single-qubit phase oracle `diag(1, exp(2πiθ))`. This is the oracle a
controlled-`U` presents to its control qubit when the target register holds an eigenvector of `U`
with eigenvalue `exp(2πiθ)` (phase kickback), so it is the eigenstate-supplied form of quantum
phase estimation (A. Kitaev, arXiv:quant-ph/9511026; R. Cleve, A. Ekert, C. Macchiavello,
M. Mosca, Proc. R. Soc. A 454, 339 (1998)).

For every precision `m` and confidence parameter `k`, the program is an adaptive dynamic circuit
(mid-circuit measurements, `.qIf`, and `.qWhile` allowed) that starts from all qubits reset and
writes an integer `res` such that `res / 2 ^ m` is within `1 / 2 ^ m` of `θ` modulo `1`, with
probability at least `1 - 1 / 2 ^ k`, for every real `θ` (runs that never terminate count as
failures; for `k = 0` the condition is empty, and `m ≤ 1` needs no oracle call). Qubit count,
non-oracle unitaries and classical conditions are free.

The resource metric is the expected number of oracle calls, evaluated semantically on the compiled
program via `CostModel.ofEmbeddedOracle`, charging `1` per oracle call and `0` for all other
operations (except any unitary step whose matrix happens to coincide with an embedded oracle call,
for example the identity when `θ` is an integer; see `CostModel.ofEmbeddedOracle`; use `.skip`
and fused steps to avoid it). The claimed bound is `phaseEstRelCost * 2 ^ m * (k + 1)`,
uniformly in `m`, `k` and `θ`, so a solution competes on the constant `phaseEstRelCost` in front
of the Heisenberg-limited scaling `2 ^ m * log (1 / δ)`.
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator ResourceCounting Real
open scoped NNReal NNRat

/-- By default we allow only a single variable. -/
inductive PhaseEst.Var where | res deriving DecidableEq, Inhabited

open PhaseEst (Var)
open PhaseEst.Var (res)

/-- Single-qubit phase oracle `diag(1, exp(2πiθ))`: `|0⟩ ↦ |0⟩`, `|1⟩ ↦ exp(2πiθ)|1⟩`. -/
noncomputable def phaseOracle (θ : ℝ) : Unitary (2 ^ 1) :=
  diagPhaseUnitary fun b : Fin (2 ^ 1) ↦ if b = 0 then 0 else θ

/-- The integer `y` is an `m`-bit estimate of `θ`: `y / 2 ^ m` is within `1 / 2 ^ m` of `θ`
modulo `1`. -/
def IsPhaseEstimate (m : ℕ) (θ : ℝ) (y : ℤ) : Prop :=
  ∃ j : ℤ, |θ - (y : ℝ) / (2 : ℝ) ^ m - (j : ℝ)| ≤ 1 / (2 : ℝ) ^ m

/-- Total number of qubits used by `phaseEstCircuit`. -/
def phaseEstQubits (m k : ℕ) : ℕ := sorry

/-- Query-model circuit on `phaseEstQubits m k` qubits with single-qubit phase-oracle calls that
writes an `m`-bit estimate of the oracle phase into `res`. -/
noncomputable def phaseEstCircuit (m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ phaseEstQubits m k)) Var (phaseEstQubits m k) 1 :=
  sorry

open QProg.Notation in
/-- Reset all qubits, then run `phaseEstCircuit` compiled with `oracle`. -/
noncomputable def phaseEstProgram (m k : ℕ)
    (oracle : Unitary (2 ^ 1)) : QProg Var (2 ^ phaseEstQubits m k) :=
  qset ;; (phaseEstCircuit m k).compile QProg.qAssign oracle

/-- `phaseEstProgram m k` writes an `m`-bit estimate of `θ` into `res` with probability at least
`1 - 1 / 2 ^ k`, for every precision `m`, confidence parameter `k` and phase `θ`. -/
theorem phaseEst_correctness (m k : ℕ) (θ : ℝ) :
    ⦃ CQAssertion.ofProb (1 - 1 / (2 : ℝ) ^ k) ⦄
    phaseEstProgram m k (phaseOracle θ)
    ⦃ fun σ ↦ ⌜IsPhaseEstimate m θ (σ res)⌝ ⦄ := by
  sorry

/-- Claimed constant in the expected oracle-call bound `phaseEstRelCost * 2 ^ m * (k + 1)`. -/
def phaseEstRelCost : ℚ≥0 := sorry

/-- Expected oracle-call bound for `phaseEstProgram m k`, uniform in `m`, `k` and `θ`. -/
theorem phaseEst_rel_cost (m k : ℕ) (θ : ℝ) :
    CostBound (CostModel.ofEmbeddedOracle (phaseOracle θ))
      (phaseEstProgram m k (phaseOracle θ))
      (phaseEstRelCost * 2 ^ m * (k + 1)) := by
  sorry

/-!
## Pinned instance

A single-number record at precision `m = 10` (additive error `1 / 1024`) and confidence `k = 10`
(failure probability at most `1 / 1024`): the expected number of oracle calls of
`phaseEstProgram` at that size is bounded by a closed constant. A solution may treat the pinned
size separately from the general family.
-/

/-- Claimed expected oracle-call bound for `phaseEstProgram` at `m = 10`, `k = 10`. -/
def phaseEstM10K10ConstCost : ℚ≥0 := sorry

/-- Expected oracle-call bound at the pinned size `m = 10`, `k = 10`, uniform in `θ`. -/
theorem phaseEst_m10_k10_const_cost (θ : ℝ) :
    CostBound (CostModel.ofEmbeddedOracle (phaseOracle θ))
      (phaseEstProgram 10 10 (phaseOracle θ))
      phaseEstM10K10ConstCost := by
  sorry

end QuantumComputation.Specs
