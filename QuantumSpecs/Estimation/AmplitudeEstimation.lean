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
public import Mathlib.LinearAlgebra.Matrix.Block
public import QuantumComputation.QuantumHoareLogic.WP

/-!
# Amplitude Estimation Specification

Query-model specification for estimating the success probability
`a = ‖(1 ⊗ ⟨1|) A |0…0⟩‖²` of an unknown `n`-qubit state-preparation unitary `A`, where the flag
is the lowest-order bit of the basis index (logical wire `0` under the little-endian `QRegister`
convention): `a` is the probability that measuring the flag of `A |0…0⟩` gives `1`
(G. Brassard, P. Høyer, M. Mosca, A. Tapp, arXiv:quant-ph/0005055).

The oracle is the `(n + 1)`-qubit select unitary `|0⟩⟨0| ⊗ A + |1⟩⟨1| ⊗ A⁻¹` on the select bit
(logical wire `0` of the oracle register) and the `n` wires of `A` (logical wires `1..n`), so one
oracle call applies `A`, its inverse, or a superposition of both, and each costs `1`. Its entry at
`(2 * x + b, 2 * y + c)` is `A x y` if `b = c = 0`, `A⁻¹ x y` if `b = c = 1`, and `0` otherwise.

For every `n`, precision `m` and confidence parameter `k`, the program is an adaptive dynamic
circuit (mid-circuit measurements, `.qIf`, and `.qWhile` allowed) that starts from all qubits
reset and writes an integer `res` with `|a - res / 2 ^ m| ≤ 1 / 2 ^ m`, with probability at least
`1 - 1 / 2 ^ k`, for every unitary `A` (runs that never terminate count as failures; for `k = 0`
the condition is empty, and `m ≤ 1` needs no oracle call). Qubit count, non-oracle unitaries and
classical conditions are free.

The resource metric is the expected number of oracle calls, evaluated semantically on the compiled
program via `CostModel.ofEmbeddedOracle`, charging `1` per oracle call and `0` for all other
operations (except any unitary step whose matrix happens to coincide with an embedded oracle call;
see `CostModel.ofEmbeddedOracle`). The claimed bound is `ampEstRelCost * 2 ^ m * (k + 1)`,
uniformly in `n`, `m`, `k` and `A`, so a solution competes on the constant `ampEstRelCost` in
front of the quadratically improved scaling `(1 / ε) * log (1 / δ)` at additive error
`ε = 1 / 2 ^ m`.
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator ResourceCounting Real
open scoped NNReal NNRat Matrix

/-- By default we allow only a single variable. -/
inductive AmpEst.Var where | res deriving DecidableEq, Inhabited

open AmpEst (Var)
open AmpEst.Var (res)

/-- Success probability of `A`: the probability that the flag (lowest-order bit of the basis
index) of `A |0…0⟩` is `1`. -/
noncomputable def ampEstAmplitude {n : ℕ} (A : Unitary (2 ^ n)) : ℝ :=
  ∑ x : Fin (2 ^ n), if x.val % 2 = 1 then ‖A.1 x ⟨0, Nat.two_pow_pos n⟩‖ ^ 2 else 0

/-- The two diagonal blocks of the select unitary: `A` for select bit `0`, `A⁻¹` for select
bit `1`. -/
noncomputable def ampEstBlocks {n : ℕ} (A : Unitary (2 ^ n)) (b : Fin 2) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  if b = 0 then A.1 else (A⁻¹).1

/-- Select unitary `|0⟩⟨0| ⊗ A + |1⟩⟨1| ⊗ A⁻¹` indexed by `Fin (2 ^ n * 2)`: under
`finProdFinEquiv : (x, b) ↦ b + 2 * x`, the block `b = 0` is `A` and the block `b = 1` is `A⁻¹`. -/
noncomputable def ampEstSelect {n : ℕ} (A : Unitary (2 ^ n)) : Unitary (2 ^ n * 2) :=
  ⟨Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.blockDiagonal (ampEstBlocks A)), by
    have h : (fun b : Fin 2 ↦ ampEstBlocks A b * (ampEstBlocks A b)ᴴ) = 1 := by
      funext b
      unfold ampEstBlocks
      split_ifs
      · exact Matrix.mem_unitaryGroup_iff.mp A.2
      · exact Matrix.mem_unitaryGroup_iff.mp (A⁻¹).2
    have key : Matrix.blockDiagonal (ampEstBlocks A) * (Matrix.blockDiagonal (ampEstBlocks A))ᴴ
        = 1 := by
      rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul, h,
        Matrix.blockDiagonal_one]
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.reindex_apply,
      Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, key, Matrix.submatrix_one_equiv]⟩

/-- Select oracle `|0⟩⟨0| ⊗ A + |1⟩⟨1| ⊗ A⁻¹` on `n + 1` qubits (`2 ^ (n + 1) = 2 ^ n * 2`
definitionally).

Under the little-endian `QRegister` convention, logical wire `0` is the select bit `b` and logical
wires `1..n` hold the `n`-qubit index `x` of `A`. -/
noncomputable def ampEstOracle {n : ℕ} (A : Unitary (2 ^ n)) : Unitary (2 ^ (n + 1)) :=
  ampEstSelect A

/-- Total number of qubits used by `ampEstCircuit`. -/
def ampEstQubits (n m k : ℕ) : ℕ := sorry

/-- Query-model circuit on `ampEstQubits n m k` qubits with `(n + 1)`-qubit select-oracle calls
that writes an `m`-bit estimate of the success probability into `res`. -/
noncomputable def ampEstCircuit (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ ampEstQubits n m k)) Var (ampEstQubits n m k) (n + 1) :=
  sorry

open QProg.Notation in
/-- Reset all qubits, then run `ampEstCircuit` compiled with `oracle`. -/
noncomputable def ampEstProgram (n m k : ℕ)
    (oracle : Unitary (2 ^ (n + 1))) : QProg Var (2 ^ ampEstQubits n m k) :=
  qset ;; (ampEstCircuit n m k).compile QProg.qAssign oracle

/-- `ampEstProgram n m k` writes into `res` an integer with
`|ampEstAmplitude A - res / 2 ^ m| ≤ 1 / 2 ^ m` with probability at least `1 - 1 / 2 ^ k`, for
every `n`, precision `m`, confidence parameter `k` and unitary `A`. -/
theorem ampEst_correctness (n m k : ℕ) (A : Unitary (2 ^ n)) :
    ⦃ CQAssertion.ofProb (1 - 1 / (2 : ℝ) ^ k) ⦄
    ampEstProgram n m k (ampEstOracle A)
    ⦃ fun σ ↦ ⌜|ampEstAmplitude A - (σ res : ℝ) / (2 : ℝ) ^ m| ≤ 1 / (2 : ℝ) ^ m⌝ ⦄ := by
  sorry

/-- Claimed constant in the expected oracle-call bound `ampEstRelCost * 2 ^ m * (k + 1)`. -/
def ampEstRelCost : ℚ≥0 := sorry

/-- Expected oracle-call bound for `ampEstProgram n m k`, uniform in `n`, `m`, `k` and `A`. -/
theorem ampEst_rel_cost (n m k : ℕ) (A : Unitary (2 ^ n)) :
    CostBound (CostModel.ofEmbeddedOracle (ampEstOracle A))
      (ampEstProgram n m k (ampEstOracle A))
      (ampEstRelCost * 2 ^ m * (k + 1)) := by
  sorry

/-!
## Pinned instance

A single-number record at precision `m = 10` (additive error `1 / 1024`) and confidence `k = 10`
(failure probability at most `1 / 1024`): the expected number of oracle calls of
`ampEstProgram` at that size is bounded by a closed constant. A solution may treat the pinned
size separately from the general family.
-/

/-- Claimed expected oracle-call bound for `ampEstProgram` at `m = 10`, `k = 10`. -/
def ampEstM10K10ConstCost : ℚ≥0 := sorry

/-- Expected oracle-call bound at the pinned size `m = 10`, `k = 10`, uniform in `n` and `A`. -/
theorem ampEst_m10_k10_const_cost (n : ℕ) (A : Unitary (2 ^ n)) :
    CostBound (CostModel.ofEmbeddedOracle (ampEstOracle A))
      (ampEstProgram n 10 10 (ampEstOracle A))
      ampEstM10K10ConstCost := by
  sorry

end QuantumComputation.Specs
