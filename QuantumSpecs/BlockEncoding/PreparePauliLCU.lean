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

public import QuantumComputation.Circuits.DynamicCircuit
public import QuantumComputation.Circuits.ResourceCounting
public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import QuantumComputation.Registers.Embed

/-!
# LCU `PREPARE` Specification

`PREPARE` is the state-preparation operation of a linear combination of unitaries (Childs and
Wiebe; Babbush et al., Section III.D). Given `b` index qubits, a number of terms `L` with
`1 ≤ L ≤ 2^b`, a precision `μ` (a number of bits), and classical rational weights
`w_0, …, w_{L-1} ≥ 0` with `λ = ∑_j w_j > 0`, the program must map the all-zero state of an index
register (`b` qubits) and a garbage register (`prepareGarbage b L μ` qubits) to a pure state
`∑_j a_j |j⟩|g_j⟩`, with unit garbage states `g_j`, whose index probabilities
`p_j = |a_j|^2` (the marginal distribution of the index register) satisfy
* `p_j = 0` for every index value `j ≥ L`, and
* `|p_j - w_j / λ| ≤ 1 / (2^μ L)` for every `j < L`.

The phases of the `a_j` and the garbage states are free: in `⟨PREP| SELECT |PREP⟩` they cancel
when `SELECT` is diagonal in the index and does not touch the garbage, so garbage entangled with
the index is allowed, as in coherent alias sampling. Clean ancillas
(`prepareAncillas b L μ` qubits) start in `|0⟩` and must be returned to `|0⟩`. The program must
act as one unitary on every input of index plus garbage, so that its inverse exists for the
reflection of a qubitized walk; only the image of the all-zero input is tied to the weights. A global
phase of the whole program is not observable and is not constrained.

Formally, there must exist a unitary `W` on index plus garbage whose column `W |0⟩` has these
index probabilities (`PrepareApproximates`), and the program must realize `W` on index plus
garbage with clean ancillas, for every input state of index plus garbage
(`RealizesCleanSubroutine`). The output from the all-zero input is then the pure state
`W |0⟩ ⊗ |0⟩`, so a program that measures the index and leaves a classical mixture, or one that
resets its registers before preparing, does not satisfy
it. The weights are classical data known when the circuit is built, so the program may depend on
them arbitrarily. The statement holds for all `b`, `L`, `μ` and all weight tables.

Encoding (the library's little-endian convention, `basisBits`): the program acts on a data
register `rData` of `b + prepareGarbage b L μ` wires followed by the ancilla register. Logical
wires `0, …, b - 1` of `rData` are the index register, wire `i` carrying bit `i` of `j` (least
significant first); the remaining wires are the garbage register. The data basis index of index
value `j` and garbage basis index `x` is `j + 2^b * x` (`prepareDataEquiv`).
In a qubitized walk the registers compose as system, then index, then garbage: the `SELECT`
specification acts on system and index (system first), this one on index and garbage.

Cost: two theorems, both over Clifford + `T` with measurements, both excluding primitive `TOFF`
gates (so each Toffoli is costed by its Clifford + `T` construction, such as `4` `T` gates with an
ancilla and a measurement), and both holding for every weight table with `w_j ≥ 0` and `λ > 0` and
every register placement. `prepare_t_cost` bounds the `T` count by the claimed
`prepareTCost b L μ` for all `b`, `1 ≤ L ≤ 2^b` and `μ`, as in the THC specification.
`prepare_b4mu8_spacetime_cost` bounds `T count * qubits` by the closed constant
`prepareB4Mu8SpacetimeCost` at the pinned size `b = 4`, `L = 16`, `μ = 8`
(`PrepareSize.b4mu8`), as in Google's arcsine specification at `k25`, where
`qubits = b + prepareGarbage b L μ + prepareAncillas b L μ` counts all index, garbage and clean
ancilla qubits. The garbage width, the ancilla count and `prepareTCost` depend only on
`(b, L, μ)`, never on the weights.

References: R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler,
H. Neven, "Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity",
Phys. Rev. X 8, 041015 (2018), arXiv:1805.03662 (Section III.D: coherent alias sampling with
`μ`-bit keep values prepares probabilities within `1 / (2^μ L)` of `w_ℓ / λ`, with a `T` count of
`4 (L + μ) + O(log L)`); A. M. Childs and N. Wiebe, arXiv:1202.5822 (linear combination of
unitaries); G. H. Low and I. L. Chuang, arXiv:1610.06546 (qubitization).
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator Matrix

/-!
## Weights, Index Probabilities and the Target Property
-/

/-- Classical table of `L` rational weights `w_0, …, w_{L-1}`. The correctness and cost theorems
assume `0 ≤ w_j` for all `j` and `0 < prepareLambda w`. -/
abbrev PrepareWeights (L : ℕ) : Type := Fin L → ℚ

/-- The `1`-norm `λ = ∑_j w_j` of a weight table. -/
def prepareLambda {L : ℕ} (w : PrepareWeights L) : ℚ :=
  ∑ j, w j

/-- Data basis index of index value `j` and garbage basis index `x`: `(j, x) ↦ j + 2^b * x`, so
the index register occupies the `b` least significant bits (the first `b` data wires). -/
def prepareDataEquiv (b g : ℕ) : Fin (2 ^ b) × Fin (2 ^ g) ≃ Fin (2 ^ (b + g)) :=
  (Equiv.prodComm _ _).trans (finProdFinEquiv.trans (finCongr (by rw [pow_add, mul_comm])))

theorem prepareDataEquiv_val (b g : ℕ) (j : Fin (2 ^ b)) (x : Fin (2 ^ g)) :
    (prepareDataEquiv b g (j, x)).val = j.val + 2 ^ b * x.val := rfl

/-- Marginal probability `p_j = ∑_x |ψ_{j, x}|^2` of index value `j` in a state `ψ` of index
(`b` qubits) plus garbage (`g` qubits). Writing `ψ = ∑_j a_j |j⟩|g_j⟩` with unit `g_j`, this is
`|a_j|^2`. -/
noncomputable def prepareIndexProb (b g : ℕ) (ψ : Fin (2 ^ (b + g)) → ℂ) (j : Fin (2 ^ b)) :
    ℝ :=
  ∑ x : Fin (2 ^ g), ‖ψ (prepareDataEquiv b g (j, x))‖ ^ 2

/-- The state `ψ` of index plus garbage prepares the weights `w` to `μ` bits: index values
`j ≥ L` have probability `0`, and every `j < L` has probability within `1 / (2^μ L)` of
`w_j / λ`. -/
def PrepareApproximates (b g L μ : ℕ) (w : PrepareWeights L) (ψ : Fin (2 ^ (b + g)) → ℂ) :
    Prop :=
  (∀ j : Fin (2 ^ b), L ≤ j.val → prepareIndexProb b g ψ j = 0) ∧
    ∀ (j : Fin (2 ^ b)) (hj : j.val < L),
      |prepareIndexProb b g ψ j - ((w ⟨j.val, hj⟩ / prepareLambda w : ℚ) : ℝ)| ≤
        1 / (2 ^ μ * L)

/-!
## Sanity Checks
-/

/-- The all-zero data state is the basis state with index `0` and garbage `0`. -/
theorem prepareDataEquiv_zero (b g : ℕ) : prepareDataEquiv b g (0, 0) = 0 :=
  Fin.ext (by simp [prepareDataEquiv_val])

/-- A basis state with index value `j₀` gives index probability `1` at `j₀` and `0` elsewhere. -/
theorem prepareIndexProb_basisState (b g : ℕ) (j₀ : Fin (2 ^ b)) (x₀ : Fin (2 ^ g))
    (j : Fin (2 ^ b)) :
    prepareIndexProb b g (basisState (prepareDataEquiv b g (j₀, x₀))) j =
      if j = j₀ then 1 else 0 := by
  unfold prepareIndexProb
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single x₀]
    · simp [basisState]
    · intro x _ hx
      simp [basisState, hx]
    · intro hx
      exact absurd (Finset.mem_univ x₀) hx
  · refine Finset.sum_eq_zero fun x _ ↦ ?_
    simp [basisState, h]

/-- Satisfiable: with `b = 0`, `L = 1` and no garbage, the identity unitary prepares every valid
one-term weight table exactly, at every precision `μ`. -/
theorem prepareApproximates_one_trivial (μ : ℕ) (w : PrepareWeights 1)
    (hsum : 0 < prepareLambda w) :
    PrepareApproximates 0 0 1 μ w ((1 : Unitary (2 ^ (0 + 0))).1 *ᵥ basisState 0) := by
  have hψ : (1 : Unitary (2 ^ (0 + 0))).1 *ᵥ basisState 0 =
      basisState (prepareDataEquiv 0 0 (0, 0)) := by
    rw [prepareDataEquiv_zero]
    exact Matrix.one_mulVec _
  have hlam : prepareLambda w = w 0 := by
    simp [prepareLambda]
  have hw0 : w 0 ≠ 0 := by
    rw [← hlam]
    exact hsum.ne'
  rw [hψ]
  refine ⟨fun j hj ↦ ?_, fun j hj ↦ ?_⟩
  · have := lt_of_lt_of_eq j.isLt (pow_zero 2)
    omega
  · have hj0 : j = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    have hwj : w ⟨j.val, hj⟩ = w 0 := congrArg w (Subsingleton.elim _ _)
    rw [prepareIndexProb_basisState, ite_eq_left hj0, hwj, hlam, div_self hw0, Rat.cast_one,
      sub_self, abs_zero]
    positivity

/-- Not vacuous: for two equal weights (`b = 1`, `L = 2`, no garbage) and `μ ≥ 1`, the state `|0⟩`,
whose index is `0` with probability `1` instead of `1 / 2`, does not have the property. -/
theorem prepareApproximates_zero_not (μ : ℕ) (hμ : 1 ≤ μ) :
    ¬ PrepareApproximates 1 0 2 μ ![1, 1] (basisState 0) := by
  rintro ⟨-, h⟩
  have h0 := h 0 (by decide)
  have hψ : (basisState 0 : Fin (2 ^ (1 + 0)) → ℂ) = basisState (prepareDataEquiv 1 0 (0, 0)) := by
    rw [prepareDataEquiv_zero]
  have hlam : prepareLambda (![1, 1] : PrepareWeights 2) = 2 := by
    norm_num [prepareLambda, Fin.sum_univ_two]
  have hw0 : (![1, 1] : PrepareWeights 2) ⟨(0 : Fin (2 ^ 1)).val, by decide⟩ = 1 := rfl
  rw [hψ, prepareIndexProb_basisState, ite_eq_left rfl, hw0, hlam] at h0
  have hc : (((1 : ℚ) / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
  have hL : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [hc, hL] at h0
  have hpow : (2 : ℝ) ≤ 2 ^ μ := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ μ := pow_le_pow_right₀ (by norm_num) hμ
  have hle : (1 : ℝ) / (2 ^ μ * 2) ≤ 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have habs := le_abs_self ((1 : ℝ) - 1 / 2)
  linarith

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive Prepare.Var where | v deriving DecidableEq, Inhabited

open Prepare (Var)
open Prepare.Var (v)

/-- Number of garbage qubits `prepareProgram` uses for `b` index qubits, `L` terms and precision
`μ`. Garbage starts in `|0⟩` and may end entangled with the index. It may not depend on the
weights. -/
def prepareGarbage (b L μ : ℕ) : ℕ := sorry

/-- Number of clean ancilla qubits `prepareProgram` uses for `b` index qubits, `L` terms and
precision `μ`. It may not depend on the weights. -/
def prepareAncillas (b L μ : ℕ) : ℕ := sorry

/-- Candidate `PREPARE` circuit for the weights `w` on `b + prepareGarbage b L μ` data wires
`rData` (`b` index wires, least significant first, followed by the garbage wires) and
`prepareAncillas b L μ` clean ancilla wires `rAnc`. -/
def prepareProgram {n : ℕ} (b L μ : ℕ) (w : PrepareWeights L)
    (rData : QRegister (b + prepareGarbage b L μ) n)
    (rAnc : QRegister (prepareAncillas b L μ) n) : DynamicCircuit Var n :=
  sorry

/-- For all `b`, `1 ≤ L ≤ 2^b`, `μ` and every weight table with `w_j ≥ 0` and `λ > 0`, there is
a unitary `W` on index plus garbage such that `W |0⟩` has index probabilities `0` on `j ≥ L` and
within `1 / (2^μ L)` of `w_j / λ` on `j < L`, and `prepareProgram` acts as `W` on every
input of index plus garbage when the ancillas start in zero, returning the ancillas to zero,
across all disjoint register placements. In particular it maps the all-zero input to the pure
state `W |0⟩ ⊗ |0⟩`. -/
theorem prepare_correctness (b L μ : ℕ) (hL : 1 ≤ L) (hLb : L ≤ 2 ^ b)
    (w : PrepareWeights L) (hw : ∀ j, 0 ≤ w j) (hsum : 0 < prepareLambda w) :
    ∃ W : Unitary (2 ^ (b + prepareGarbage b L μ)),
      PrepareApproximates b (prepareGarbage b L μ) L μ w (W.1 *ᵥ basisState 0) ∧
      ∀ {n : ℕ}
        (rData : QRegister (b + prepareGarbage b L μ) n)
        (rAnc : QRegister (prepareAncillas b L μ) n)
        (hdisj : rData.DisjointWires rAnc),
        RealizesCleanSubroutine rData rAnc hdisj W
          (prepareProgram b L μ w rData rAnc).compile := by sorry

/-- `T`-gate count of `prepareProgram`. -/
abbrev prepareTCount {n : ℕ} (b L μ : ℕ) (w : PrepareWeights L)
    (rData : QRegister (b + prepareGarbage b L μ) n)
    (rAnc : QRegister (prepareAncillas b L μ) n) : ℕ :=
  (prepareProgram b L μ w rData rAnc).count PrimitiveGate.T

/-- Declared qubits: `b` index qubits, `prepareGarbage b L μ` garbage qubits and
`prepareAncillas b L μ` clean ancillas. -/
abbrev prepareQubits (b L μ : ℕ) : ℕ :=
  b + prepareGarbage b L μ + prepareAncillas b L μ

/-!
## `T`-Count Cost Theorem

The cost theorem forbids primitive `TOFF` gates and bounds the `T` count by the claimed
`prepareTCost b L μ`, for all sizes, every valid weight table and every register placement.
-/

/-- Claimed `T` count of `prepareProgram` for `b` index qubits, `L` terms and precision `μ`. It
depends only on `(b, L, μ)`. -/
def prepareTCost (b L μ : ℕ) : ℕ := sorry

/-- For all `b`, `1 ≤ L ≤ 2^b`, `μ`, every weight table with `w_j ≥ 0` and `λ > 0`, and every
register placement, `prepareProgram` uses no `TOFF` gates and at most `prepareTCost b L μ` `T`
gates. -/
theorem prepare_t_cost (b L μ : ℕ) (hL : 1 ≤ L) (hLb : L ≤ 2 ^ b)
    (w : PrepareWeights L) (hw : ∀ j, 0 ≤ w j) (hsum : 0 < prepareLambda w) {n : ℕ}
    (rData : QRegister (b + prepareGarbage b L μ) n)
    (rAnc : QRegister (prepareAncillas b L μ) n) :
    (prepareProgram b L μ w rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      prepareTCount b L μ w rData rAnc ≤ prepareTCost b L μ := by sorry

/-!
## Spacetime Cost Theorem at the Pinned Size

The cost theorem forbids primitive `TOFF` gates and bounds `T count * qubits` by a closed `ℕ`
constant at `PrepareSize.b4mu8` (`b = 4` index qubits, `L = 16 = 2^b` terms, `μ = 8`), for every
weight table with `w_j ≥ 0` and `λ > 0` and every register placement.
-/

/-- Sizes of a `PREPARE` instance: `b` index qubits, `L` terms, precision `μ`. -/
structure PrepareSize where
  /-- Number of index qubits. -/
  b : ℕ
  /-- Number of terms. -/
  L : ℕ
  /-- Precision of the keep values. -/
  μ : ℕ

/-- The pinned size `b = 4`, `L = 16`, `μ = 8`. -/
abbrev PrepareSize.b4mu8 : PrepareSize where
  b := 4
  L := 16
  μ := 8

/-- Claimed spacetime cost (`T count * qubits`) of `prepareProgram` at `PrepareSize.b4mu8`. -/
def prepareB4Mu8SpacetimeCost : ℕ := sorry

/-- At `PrepareSize.b4mu8`, for every weight table with `w_j ≥ 0` and `λ > 0` and every register
placement, `prepareProgram` uses no `TOFF` gates and has `T count * (b + garbage + ancillas)` at
most `prepareB4Mu8SpacetimeCost`. -/
theorem prepare_b4mu8_spacetime_cost
    (w : PrepareWeights PrepareSize.b4mu8.L) (hw : ∀ j, 0 ≤ w j) (hsum : 0 < prepareLambda w)
    {n : ℕ}
    (rData : QRegister (PrepareSize.b4mu8.b +
      prepareGarbage PrepareSize.b4mu8.b PrepareSize.b4mu8.L PrepareSize.b4mu8.μ) n)
    (rAnc : QRegister (prepareAncillas PrepareSize.b4mu8.b PrepareSize.b4mu8.L
      PrepareSize.b4mu8.μ) n) :
    (prepareProgram PrepareSize.b4mu8.b PrepareSize.b4mu8.L PrepareSize.b4mu8.μ w rData
        rAnc).count PrimitiveGate.TOFF = 0 ∧
      prepareTCount PrepareSize.b4mu8.b PrepareSize.b4mu8.L PrepareSize.b4mu8.μ w rData rAnc *
        prepareQubits PrepareSize.b4mu8.b PrepareSize.b4mu8.L PrepareSize.b4mu8.μ ≤
      prepareB4Mu8SpacetimeCost := by sorry

end QuantumComputation.Specs
