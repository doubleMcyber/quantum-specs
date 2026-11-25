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
import LowerBounds.Grover.ParallelStatement
import LowerBounds.Grover.ParallelDefs
import LowerBounds.Grover.ParallelCost
import LowerBounds.Grover.ThreeFifthsBound
import Mathlib

/-!
# The link at cell `(m, k)` between the specification and the branch semantics

The run index is `KSet n k`; run `S` applies `groverParallelMarkingOracle m S` at every oracle node
(`GK`). `goodAny` and `goodAll` are the find-any and find-all success predicates on a store.
`expect_programOf`, `cwaK_le`, `succAny_eq` and `succAll_eq` carry `GroverLowerBound.expect_findAny`,
`GroverThreeFifths.cwa_le` and `GroverThreeFifths.succ_eq` over to this run index, and
`card_goodAny_le`, `card_goodAll_le` bound the number of runs a store satisfies.
-/

open QuantumComputation.Specs Operator ResourceCounting Filter
open scoped Matrix QHLExpectation ComplexOrder MatrixOrder ENNReal NNReal
open QuantumComputation.Specs.Grover (Var)
open QuantumComputation.Specs.Grover.Var (res)

namespace GroverParallel

open GroverLowerBound

/-- the oracle family indexed by the k-sets (every round, every register) -/
noncomputable def GK (n m k Q : ℕ) :
    KSet n k → ℕ → QRegister ((n + 1) * m) Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ :=
  fun S _ r ↦ (r.embedUnitary (groverParallelMarkingOracle m S.1)).1

/-- find-any success predicate on (store, run index) -/
def goodAny (n k : ℕ) (σ : Store Var) (S : KSet n k) : Prop := ∃ x ∈ S.1, σ res = (x.val : ℤ)

/-- find-all success predicate on (store, run index) -/
def goodAll (n k : ℕ) (σ : Store Var) (S : KSet n k) : Prop := decodeTargets n k (σ res) = S.1

noncomputable instance (n k : ℕ) (σ : Store Var) (S : KSet n k) : Decidable (goodAny n k σ S) :=
  Classical.propDecidable _

noncomputable instance (n k : ℕ) (σ : Store Var) (S : KSet n k) : Decidable (goodAll n k σ S) :=
  Classical.propDecidable _

section link

variable {n m k Q : ℕ}

private lemma hGK (S : KSet n k) (j : ℕ) (r : QRegister ((n + 1) * m) Q) :
    GK n m k Q S j r = (r.embedUnitary (groverParallelMarkingOracle m S.1)).1 := rfl

lemma expect_programOf (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m))
    (S : Finset (Fin (2 ^ n))) (Δ : CQState (Store Var) (2 ^ Q))
    (Ψ : CQAssertion (Store Var) (2 ^ Q)) :
    𝔼[(interp (programOf c S)).toStateFun Δ ⊨ Ψ] =
      𝔼[(interp (c.compile QProg.qAssign (groverParallelMarkingOracle m S))).toStateFun
        (CQState.qSet Δ) ⊨ Ψ] := by
  rw [← expect_wp, ← expect_wp]
  simp only [programOf, wp_qSeq, wp_qSet]
  exact expect_qSet _ _

/-- The oracle-count weight of the real run on the unrolled program is at most the cost bound. -/
lemma cwaK_le (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m))
    (σ₀ : Store Var) (S : KSet n k) (Δ₀ : CQState (Store Var) (2 ^ Q)) (htr : Δ₀.trace = 1)
    (hrep : Rep (CQState.qSet Δ₀) [(initBranch σ₀ : Branch Var (KSet n k) Q)] S) (qS : ℝ≥0)
    (hq : CostBound (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S.1))
      (programOf c S.1) qS) (M : ℕ) :
    GroverThreeFifths.cwa S (ens (GK n m k Q) (unroll M c) [(initBranch σ₀ : Branch Var (KSet n k) Q)])
      ≤ (qS : ℝ) := by
  have h1 := GroverThreeFifths.rep_cost_all (i₀ := S) (groverParallelMarkingOracle m S.1) (GK n m k Q)
    (hGK S) (unroll M c) hrep
  have h0 : GroverThreeFifths.cwa S [(initBranch σ₀ : Branch Var (KSet n k) Q)] = 0 := by
    simp [GroverThreeFifths.cwa, initBranch]
  rw [h0, sub_zero] at h1
  have h2 := unroll_cost_le (groverParallelMarkingOracle m S.1) c (CQState.qSet Δ₀)
    (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S.1)) M
  have h3 := hq Δ₀
  have h4 : expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S.1))
      (programOf c S.1) Δ₀ =
      expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S.1))
        (c.compile QProg.qAssign (groverParallelMarkingOracle m S.1)) (CQState.qSet Δ₀) := by
    simp [programOf]
  rw [h4, htr] at h3
  have h5 := h1.trans (h2.trans h3)
  simp only [ENNReal.coe_one, one_mul] at h5
  have := (ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top).1 h5
  simpa using this

/-- The find-any success expectation of the unrolled program is the success weight of the
branches. -/
lemma succAny_eq (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m))
    (σ₀ : Store Var) (S : KSet n k) (Δ₀ : CQState (Store Var) (2 ^ Q))
    (hrep : Rep (CQState.qSet Δ₀) [(initBranch σ₀ : Branch Var (KSet n k) Q)] S) (M : ℕ) :
    𝔼[(interp ((unroll M c).compile (groverParallelMarkingOracle m S.1))).toStateFun
        (CQState.qSet Δ₀) ⊨ fun σ ↦ ⌜∃ x ∈ S.1, σ res = x.val⌝] =
      succG (goodAny n k) S
        (ens (GK n m k Q) (unroll M c) [(initBranch σ₀ : Branch Var (KSet n k) Q)]) := by
  have hR := rep_interp (i₀ := S) (groverParallelMarkingOracle m S.1) (GK n m k Q)
    (hGK S) (unroll M c) hrep
  exact rep_post (fun σ : Store Var ↦ goodAny n k σ S) hR

/-- The find-all success expectation of the unrolled program is the success weight of the
branches. -/
lemma succAll_eq (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m))
    (σ₀ : Store Var) (S : KSet n k) (Δ₀ : CQState (Store Var) (2 ^ Q))
    (hrep : Rep (CQState.qSet Δ₀) [(initBranch σ₀ : Branch Var (KSet n k) Q)] S) (M : ℕ) :
    𝔼[(interp ((unroll M c).compile (groverParallelMarkingOracle m S.1))).toStateFun
        (CQState.qSet Δ₀) ⊨ fun σ ↦ ⌜decodeTargets n k (σ res) = S.1⌝] =
      succG (goodAll n k) S
        (ens (GK n m k Q) (unroll M c) [(initBranch σ₀ : Branch Var (KSet n k) Q)]) := by
  have hR := rep_interp (i₀ := S) (groverParallelMarkingOracle m S.1) (GK n m k Q)
    (hGK S) (unroll M c) hrep
  exact rep_post (fun σ : Store Var ↦ goodAll n k σ S) hR

end link

/-! ### Cardinalities of the good sets -/

lemma card_goodAll_le {n k : ℕ} (σ : Store Var) :
    (Finset.univ.filter (goodAll n k σ)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have ha' : decodeTargets n k (σ res) = a.1 := ha
  have hb' : decodeTargets n k (σ res) = b.1 := hb
  exact Subtype.ext (ha'.symm.trans hb')

lemma card_goodAny_le {n k : ℕ} (hk : 1 ≤ k) (σ : Store Var) :
    (Finset.univ.filter (goodAny n k σ)).card ≤ (2 ^ n - 1).choose (k - 1) := by
  by_cases hx : ∃ x0 : Fin (2 ^ n), σ res = (x0.val : ℤ)
  · obtain ⟨x0, hx0⟩ := hx
    -- in a good set, the item that matches `σ res` is `x0`
    have hmem : ∀ S : KSet n k, goodAny n k σ S → x0 ∈ S.1 := by
      rintro S ⟨x, hxS, hxσ⟩
      have : x = x0 := Fin.ext (by exact_mod_cast hxσ.symm.trans hx0)
      rw [← this]
      exact hxS
    have hcard : ∀ S : KSet n k, S.1.card = k := by
      intro S
      have := S.2
      simp only [groverTargetSets, Finset.mem_powersetCard] at this
      exact this.2
    refine le_trans (Finset.card_le_card_of_injOn (fun S : KSet n k => S.1.erase x0)
      (t := Finset.powersetCard (k - 1) (Finset.univ.erase x0)) ?_ ?_) ?_
    · intro S hS
      have hS' : goodAny n k σ S := by simpa using hS
      have hx0S := hmem S hS'
      simp only [Finset.mem_coe, Finset.mem_powersetCard]
      refine ⟨Finset.erase_subset_erase _ (Finset.subset_univ _), ?_⟩
      rw [Finset.card_erase_of_mem hx0S, hcard S]
    · intro S hS T hT hST
      have hS' : goodAny n k σ S := by simpa using hS
      have hT' : goodAny n k σ T := by simpa using hT
      apply Subtype.ext
      have h1 : S.1 = insert x0 (S.1.erase x0) := (Finset.insert_erase (hmem S hS')).symm
      have h2 : T.1 = insert x0 (T.1.erase x0) := (Finset.insert_erase (hmem T hT')).symm
      have hST' : S.1.erase x0 = T.1.erase x0 := hST
      rw [h1, h2, hST']
    · rw [Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ _)]
      simp
  · have : Finset.univ.filter (goodAny n k σ) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro S - ⟨x, _, hxσ⟩
      exact hx ⟨x, hxσ⟩
    rw [this]
    simp

end GroverParallel

#print axioms GroverParallel.expect_programOf
#print axioms GroverParallel.cwaK_le
#print axioms GroverParallel.succAny_eq
#print axioms GroverParallel.succAll_eq
#print axioms GroverParallel.card_goodAll_le
#print axioms GroverParallel.card_goodAny_le
