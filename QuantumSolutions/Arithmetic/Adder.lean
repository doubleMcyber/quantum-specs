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
public import QuantumComputationDiscoveries.Primitives.Arcsin.Solution.EqualTableAdd

/-!
# In-Place Addition (`adder`) Specification: Baseline Solution

Baseline: the ripple-carry adder with temporary-AND carries and measurement-based uncomputation
(Gidney 2018), taken from the step list `ArcsinImpl.rippleSteps` of the `arcsin` solution in
`QuantumComputationDiscoveries`. It uses `k` clean ancillas (one zero carry-in wire and `k - 1`
carry wires) and at most `4 * (k - 1)` `T` gates. The specification text below is unchanged; only
the holes are filled and the theorems proved.

Parameterized specification for reversible in-place addition of two `k`-bit quantum registers,
`|x⟩|b⟩|0⟩^⊗m ↦ |x⟩|(b + x) mod 2^k⟩|0⟩^⊗m`, for every bit-width `k`. Both registers hold unsigned
integers in `[0, 2^k)`, least-significant bit first. The addend `x` is preserved, the target `b` is
overwritten by the sum modulo `2^k` (no carry-out qubit), and the `m` clean ancilla qubits are
returned to zero. Kets are written with the most significant register on the left, so the rightmost
register occupies the lowest wires. Since addition modulo `2^k` is the same map for unsigned and for
two's-complement integers, the specification covers both.

There are two resource metrics over Clifford + `T` with measurements: the `T` count, and spacetime
(`T count * qubits`), where `qubits = 2 * k + adderAncillas k` is the total number of data and clean
ancilla qubits. Each metric has three cost theorems. One bounds the cost at every bit-width `k` by a
claimed function of `k`. The other two pin the bit-widths `k = 64` and `k = 2048` and bound the cost
by a claimed closed constant, so that two solutions can be compared by a number. `TOFF` gates are
excluded, so each Toffoli is costed by its Clifford + `T` construction, such as `4` `T` gates with
an ancilla and a measurement (C. Jones, Phys. Rev. A 87, 022328 (2013)).

References for the textbook constructions:
* S. A. Cuccaro, T. G. Draper, S. A. Kutin, D. P. Moulton, "A new quantum ripple-carry addition
  circuit", arXiv:quant-ph/0410184 (one ancilla, `2k - 1` Toffolis without carry-out).
* C. Gidney, "Halving the cost of quantum addition", Quantum 2, 74 (2018), arXiv:1709.06648
  (`k - 1` ancillas, `4k + O(1)` `T` gates with measurement-based uncomputation).
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator

/-!
## Reversible In-Place Addition Unitary
-/

/-- Ideal `2k`-qubit unitary `|x⟩|b⟩ ↦ |x⟩|(b + x) mod 2^k⟩`: the basis permutation
`equalTableAddPerm` of the identity table, which splits a basis index of `Fin (2 ^ (2 * k))` into
the addend `x` (high half) and the target `b` (low half). -/
noncomputable abbrev adderUnitary (k : ℕ) : Unitary (2 ^ (2 * k)) :=
  permutationUnitary (equalTableAddPerm (fun x : Fin (2 ^ k) ↦ x))

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive Adder.Var where | v deriving DecidableEq, Inhabited

open Adder (Var)
open Adder.Var (v)

/-!
## Baseline Construction
-/

namespace AdderImpl

open ArcsinImpl ArcsinImpl.Step

variable {n : ℕ}

/-- Value of `equalTableAddPerm f` on a basis index with low half `b` and high half `x`. Copied
from `equalTableAddPerm_val_of_eq` in the `arcsin` solution (`StageProofB`), to avoid importing its
tables. -/
theorem equalTableAddPerm_val {k : ℕ} (f : Fin (2 ^ k) → Fin (2 ^ k))
    (j : Fin (2 ^ (2 * k))) (b x : Fin (2 ^ k))
    (hb : j.val % 2 ^ k = b.val) (hx : j.val / 2 ^ k = x.val) :
    ((equalTableAddPerm f) j : ℕ) = (b.val + (f x).val) % 2 ^ k + 2 ^ k * x.val := by
  have hjx : (Fin.cast (by rw [two_mul, pow_add]) j).divNat = x :=
    Fin.ext (by simp [Fin.divNat, hx])
  simp [equalTableAddPerm, splitEqualBasisEquiv, splitBasisEquiv, addRightShear,
    finProdFinEquiv_symm_apply, hjx, Fin.modNat, hb, Fin.val_add]

/-- Ripple-carry addition of the addend (high `k` data wires) into the target (low `k` data
wires), with zero carry-in wire `rAnc 0` and the other `k - 1` ancilla wires as carries. -/
def adderSteps : (k : ℕ) → QRegister (2 * k) n → QRegister k n → List (Step n)
  | 0, _, _ => []
  | K + 1, rData, rAnc =>
      rippleSteps K (rData.slice (K + 1) (K + 1) (by omega)) (rData.slice 0 (K + 1) (by omega))
        (rAnc 0) (regTail rAnc)

theorem andCount_adderSteps (k : ℕ) (rData : QRegister (2 * k) n) (rAnc : QRegister k n) :
    ((adderSteps k rData rAnc).map Step.andCount).sum = k - 1 := by
  cases k with
  | zero => rfl
  | succ K =>
    rw [adderSteps, andCount_rippleSteps]
    rfl

theorem runList_adderSteps (k : ℕ) (rData : QRegister (2 * k) n) (rAnc : QRegister k n)
    (hdisj : rData.DisjointWires rAnc) (σ : Equiv.Perm (Fin (2 ^ (2 * k))))
    (hσ : ∀ j, (σ j : ℕ) = (j % 2 ^ k + j / 2 ^ k) % 2 ^ k + 2 ^ k * (j / 2 ^ k))
    (β : BitAssignment n) (hβ : localIdx rAnc β = 0) :
    runList (adderSteps k rData rAnc) β =
      some (writeReg β rData (basisBits (2 * k) (σ (localIdx rData β)))) := by
  cases k with
  | zero =>
    have h : σ (localIdx rData β) = localIdx rData β := Fin.ext (by
      rw [hσ]
      simp only [pow_zero, Nat.mod_one, Nat.div_one, one_mul, zero_add])
    rw [adderSteps, runList_nil, h, basisBits_basisBitsEquiv_symm, writeReg_self]
  | succ K =>
    have hclean := eq_zero_of_localIdx_eq_zero rAnc β hβ
    have hci : β (rAnc 0) = 0 := hclean 0
    have hBA : (rData.slice 0 (K + 1) (by omega)).DisjointWires
        (rData.slice (K + 1) (K + 1) (by omega)) :=
      QRegister.slice_disjoint_of_le rData 0 (K + 1) (K + 1) (K + 1)
        (by omega) (by omega) (by omega)
    have hDA : ∀ {a b : ℕ} (r : QRegister a (2 * (K + 1))) (r' : QRegister b (K + 1)),
        (rData.compose r).DisjointWires (rAnc.compose r') := fun _ _ ↦
      (hdisj.compose_left _).compose_right _
    rw [adderSteps, runList_rippleSteps K _ _ _ _ (QRegister.disjoint_comm.mp hBA) (hDA _ _)
      (hDA _ _) (fun ⟨_, h⟩ ↦ hdisj.ne _ _ h) (fun ⟨_, h⟩ ↦ hdisj.ne _ _ h)
      (zero_not_mem_regTail rAnc) β (fun i ↦ by rw [regTail_apply]; exact hclean _)]
    refine congrArg some ?_
    rw [← writeReg_eq_of_eqOn β (writeReg β (rData.slice 0 (K + 1) (by omega)) _) rData
      fun w hw ↦ writeReg_apply_of_not_mem _ _ _ _ fun ⟨i, h⟩ ↦ hw ⟨_, h⟩]
    congr 1
    rw [← basisBits_basisBitsEquiv_symm (2 * (K + 1)) (fun p ↦ _)]
    congr 1
    apply Fin.ext
    have hB := (localIdx (rData.slice 0 (K + 1) (by omega)) β).isLt
    rw [hσ, localIdx_val_split rData (K + 1) (K + 1) (by omega) β, ← localIdx,
      localIdx_val_split rData (K + 1) (K + 1) (by omega), localIdx_writeReg,
      basisBitsEquiv_symm_basisBits, localIdx_writeReg_of_disjoint _ _ _ hBA,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hB, Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt hB, hci]
    simp only [zero_add, ZMod.val_zero, add_zero]
    congr 2
    exact Nat.add_comm _ _

end AdderImpl

open ArcsinImpl ArcsinImpl.Step

/-- Number of clean ancilla qubits `adderProgram` uses at bit-width `k`. -/
def adderAncillas (k : ℕ) : ℕ := k

/-- Parameterized in-place adder on `2 * k` data wires `rData` (`k` target wires `b` followed by `k`
addend wires `x`, each least-significant bit first, matching `finProdFinEquiv`) and
`adderAncillas k` clean ancilla wires `rAnc`. -/
def adderProgram {n : ℕ} (k : ℕ)
    (rData : QRegister (2 * k) n)
    (rAnc : QRegister (adderAncillas k) n) : DynamicCircuit Var n :=
  compileList v (AdderImpl.adderSteps k rData rAnc)

/-- Parameterized correctness theorem: for every bit-width `k`, `adderProgram k` realizes
`adderUnitary k` as an exact clean subroutine across all disjoint register placements. -/
theorem adder_correctness (k : ℕ) :
    ∀ {n : ℕ}
      (rData : QRegister (2 * k) n)
      (rAnc : QRegister (adderAncillas k) n)
      (hdisj : rData.DisjointWires rAnc),
      RealizesCleanSubroutine rData rAnc hdisj (adderUnitary k)
        (adderProgram k rData rAnc).compile := by
  intro n rData rAnc hdisj
  refine realizesCleanSubroutine_compileList v _ rData rAnc hdisj
    (equalTableAddPerm (fun x : Fin (2 ^ k) ↦ x)) fun β hβ ↦ ?_
  refine AdderImpl.runList_adderSteps k rData rAnc hdisj _ (fun j ↦ ?_) β hβ
  have hdiv_lt : j.val / 2 ^ k < 2 ^ k :=
    Nat.div_lt_of_lt_mul (lt_of_lt_of_eq j.isLt (by rw [two_mul, pow_add]))
  exact AdderImpl.equalTableAddPerm_val (fun x ↦ x) j
    ⟨j.val % 2 ^ k, Nat.mod_lt _ (by positivity)⟩ ⟨j.val / 2 ^ k, hdiv_lt⟩ rfl rfl

/-- `T`-gate count of `adderProgram k`, which the cost predicates require to use no `TOFF` gates. -/
abbrev adderTCount {n : ℕ} (k : ℕ)
    (rData : QRegister (2 * k) n)
    (rAnc : QRegister (adderAncillas k) n) : ℕ :=
  (adderProgram k rData rAnc).count PrimitiveGate.T

/-- Spacetime cost `T count * qubits` of `adderProgram k`, counting all `2 * k + adderAncillas k`
data and clean ancilla qubits. -/
abbrev adderSpacetime {n : ℕ} (k : ℕ)
    (rData : QRegister (2 * k) n)
    (rAnc : QRegister (adderAncillas k) n) : ℕ :=
  adderTCount k rData rAnc * (2 * k + adderAncillas k)

/-!
## Cost Predicates

Both predicates forbid primitive `TOFF` gates (so every Toffoli must be decomposed into Clifford +
`T` + measurements) and bound a cost of `adderProgram` at bit-width `k` across all register
placements.
-/

/-- `adderProgram` at bit-width `k` uses no primitive `TOFF` gates and has `T` count at most `cost`,
across all register placements. -/
abbrev SatisfiesAdderTBound (k cost : ℕ) : Prop :=
  ∀ {n : ℕ}
    (rData : QRegister (2 * k) n)
    (rAnc : QRegister (adderAncillas k) n),
    (adderProgram k rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      adderTCount k rData rAnc ≤ cost

/-- `adderProgram` at bit-width `k` uses no primitive `TOFF` gates and has spacetime cost at most
`cost`, for every constant and register placement it can be given. -/
abbrev SatisfiesAdderSpacetimeBound (k cost : ℕ) : Prop :=
  ∀ {n : ℕ}
    (rData : QRegister (2 * k) n)
    (rAnc : QRegister (adderAncillas k) n),
    (adderProgram k rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      adderSpacetime k rData rAnc ≤ cost

/-- The baseline uses no `TOFF` gates and at most `4 * (k - 1)` `T` gates. -/
theorem adder_baseline_t_bound (k : ℕ) : SatisfiesAdderTBound k (4 * (k - 1)) := by
  intro n rData rAnc
  refine ⟨count_TOFF_compileList v _, ?_⟩
  have h := count_T_compileList v (AdderImpl.adderSteps k rData rAnc)
  exact h.trans (le_of_eq (congrArg (4 * ·) (AdderImpl.andCount_adderSteps k rData rAnc)))

/-- The baseline has spacetime cost at most `4 * (k - 1) * (2 * k + k)`. -/
theorem adder_baseline_spacetime_bound (k : ℕ) :
    SatisfiesAdderSpacetimeBound k (4 * (k - 1) * (2 * k + k)) := by
  intro n rData rAnc
  exact ⟨(adder_baseline_t_bound k rData rAnc).1,
    Nat.mul_le_mul_right _ (adder_baseline_t_bound k rData rAnc).2⟩

/-!
## Cost Theorems at Every Bit-Width
-/

/-- Claimed `T` count of `adderProgram`, as a function of the bit-width `k`. -/
def adderTCost (k : ℕ) : ℕ := 4 * (k - 1)

theorem adder_t_cost (k : ℕ) :
    SatisfiesAdderTBound k (adderTCost k) :=
  adder_baseline_t_bound k

/-- Claimed spacetime cost of `adderProgram`, as a function of the bit-width `k`. -/
def adderSpacetimeCost (k : ℕ) : ℕ := 4 * (k - 1) * (2 * k + k)

theorem adder_spacetime_cost (k : ℕ) :
    SatisfiesAdderSpacetimeBound k (adderSpacetimeCost k) :=
  adder_baseline_spacetime_bound k

/-!
## Cost Theorems at the Pinned Bit-Widths `k = 64` and `k = 2048`
-/

/-- Claimed `T` count bound for `adderProgram` at `k = 64`. -/
def adderK64TCost : ℕ := 252

theorem adder_k64_t_cost :
    SatisfiesAdderTBound 64 adderK64TCost :=
  adder_baseline_t_bound 64

/-- Claimed spacetime cost bound for `adderProgram` at `k = 64`. -/
def adderK64SpacetimeCost : ℕ := 48384

theorem adder_k64_spacetime_cost :
    SatisfiesAdderSpacetimeBound 64 adderK64SpacetimeCost :=
  adder_baseline_spacetime_bound 64

/-- Claimed `T` count bound for `adderProgram` at `k = 2048`. -/
def adderK2048TCost : ℕ := 8188

theorem adder_k2048_t_cost :
    SatisfiesAdderTBound 2048 adderK2048TCost :=
  adder_baseline_t_bound 2048

/-- Claimed spacetime cost bound for `adderProgram` at `k = 2048`. -/
def adderK2048SpacetimeCost : ℕ := 50307072

theorem adder_k2048_spacetime_cost :
    SatisfiesAdderSpacetimeBound 2048 adderK2048SpacetimeCost :=
  adder_baseline_spacetime_bound 2048

end QuantumComputation.Specs
