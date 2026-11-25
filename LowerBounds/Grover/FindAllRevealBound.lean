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
import LowerBounds.Grover.FindAllRevealWeight
import LowerBounds.Grover.ParallelBound
import LowerBounds.Grover.ParallelLink
import LowerBounds.Grover.ParallelOracle
import LowerBounds.Grover.ParallelCost
import Mathlib

/-!
# The find-any argument for the last target

`reveal_core`: fix a `(k - 1)`-set `K` with `4 m ≤ 2 ^ n - (k - 1)`. For a circuit with `m` slots
that meets Google's find-all specification and certified costs `q S`, the average of
`q (insert x K)` over the `2 ^ n - (k - 1)` addresses `x ∉ K` is at least `(π / 8 + 1 / 4) t - 4 / t`
with `t = √((2 ^ n - (k - 1)) / m)`. The proof runs the argument of `ParallelBound.lean` over the
addresses outside `K`, with the oracle for `K` as the common part of every call
(`pwS_ens_mono_W`).
-/

open QuantumComputation.Specs Operator ResourceCounting Filter Real
open scoped Matrix QHLExpectation ComplexOrder MatrixOrder ENNReal NNReal
open QuantumComputation.Specs.Grover (Var)
open QuantumComputation.Specs.Grover.Var (res)

namespace GroverParallel

open GroverLowerBound

/-! ### The run index and the oracle families -/

private abbrev RIdx (n : ℕ) (K : Finset (Fin (2 ^ n))) : Type := {x : Fin (2 ^ n) // x ∉ K}

private noncomputable def GR (n m Q : ℕ) (K : Finset (Fin (2 ^ n))) :
    RIdx n K → ℕ → QRegister ((n + 1) * m) Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ :=
  fun x _ r ↦ (r.embedUnitary (groverParallelMarkingOracle m (insert x.1 K))).1

private noncomputable def GR1 (n m Q : ℕ) (K : Finset (Fin (2 ^ n))) :
    RIdx n K → ℕ → QRegister ((n + 1) * m) Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ :=
  fun x _ r ↦ (r.embedUnitary (groverParallelMarkingOracle m {x.1})).1

private noncomputable def WR (n m Q : ℕ) (K : Finset (Fin (2 ^ n))) :
    ℕ → QRegister ((n + 1) * m) Q → Unitary (2 ^ Q) :=
  fun _ r ↦ r.embedUnitary (groverParallelMarkingOracle m K)

/-- find-all success predicate at the run `insert x K` -/
private def goodR (n k : ℕ) (K : Finset (Fin (2 ^ n))) (σ : Store Var) (x : RIdx n K) : Prop :=
  decodeTargets n k (σ res) = insert x.1 K

private noncomputable instance (n k : ℕ) (K : Finset (Fin (2 ^ n))) (σ : Store Var)
    (x : RIdx n K) : Decidable (goodR n k K σ x) :=
  Classical.propDecidable _

private lemma card_RIdx {n : ℕ} (K : Finset (Fin (2 ^ n))) :
    Fintype.card (RIdx n K) = 2 ^ n - K.card := by
  have h1 : Fintype.card (RIdx n K) = (Finset.univ.filter (fun x : Fin (2 ^ n) ↦ x ∉ K)).card :=
    Fintype.card_subtype _
  have h2 : Finset.univ.filter (fun x : Fin (2 ^ n) ↦ x ∉ K) = Kᶜ := by
    ext x; simp
  rw [h1, h2, Finset.card_compl, Fintype.card_fin]

private lemma sum_RIdx {n : ℕ} (K : Finset (Fin (2 ^ n))) (g : Fin (2 ^ n) → ℝ) :
    ∑ x : RIdx n K, g x.1 = ∑ x ∈ Finset.univ.filter (fun x : Fin (2 ^ n) ↦ x ∉ K), g x :=
  (Finset.sum_subtype _ (fun x ↦ by simp) g).symm

private lemma card_goodR_le {n k : ℕ} (K : Finset (Fin (2 ^ n))) (σ : Store Var) :
    (Finset.univ.filter (goodR n k K σ)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have ha' : decodeTargets n k (σ res) = insert a.1 K := ha
  have hb' : decodeTargets n k (σ res) = insert b.1 K := hb
  have h : insert a.1 K = insert b.1 K := ha'.symm.trans hb'
  have hmem : a.1 ∈ insert b.1 K := by rw [← h]; exact Finset.mem_insert_self _ _
  rcases Finset.mem_insert.1 hmem with h1 | h1
  · exact Subtype.ext h1
  · exact absurd h1 a.2

private lemma insert_mem_targets {n k : ℕ} (hk : 1 ≤ k) (K : Finset (Fin (2 ^ n)))
    (hK : K.card = k - 1) (x : RIdx n K) : insert x.1 K ∈ groverTargetSets n k := by
  simp only [groverTargetSets, Finset.mem_powersetCard]
  refine ⟨Finset.subset_univ _, ?_⟩
  rw [Finset.card_insert_of_notMem x.2, hK]
  omega

/-! ### The two link facts at run index `RIdx n K` -/

section link

variable {n m k Q : ℕ}

private lemma cwaR_le (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m))
    (K : Finset (Fin (2 ^ n)))
    (σ₀ : Store Var) (x : RIdx n K) (Δ₀ : CQState (Store Var) (2 ^ Q)) (htr : Δ₀.trace = 1)
    (hrep : Rep (CQState.qSet Δ₀) [(initBranch σ₀ : Branch Var (RIdx n K) Q)] x) (qS : ℝ≥0)
    (hq : CostBound (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m (insert x.1 K)))
      (programOf c (insert x.1 K)) qS) (M : ℕ) :
    GroverThreeFifths.cwa x (ens (GR n m Q K) (unroll M c) [(initBranch σ₀ : Branch Var (RIdx n K) Q)])
      ≤ (qS : ℝ) := by
  have h1 := GroverThreeFifths.rep_cost_all (i₀ := x) (groverParallelMarkingOracle m (insert x.1 K))
    (GR n m Q K) (fun _ _ ↦ rfl) (unroll M c) hrep
  have h0 : GroverThreeFifths.cwa x [(initBranch σ₀ : Branch Var (RIdx n K) Q)] = 0 := by
    simp [GroverThreeFifths.cwa, initBranch]
  rw [h0, sub_zero] at h1
  have h2 := unroll_cost_le (groverParallelMarkingOracle m (insert x.1 K)) c (CQState.qSet Δ₀)
    (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m (insert x.1 K))) M
  have h3 := hq Δ₀
  have h4 : expectedCost (CostModel.ofEmbeddedOracle
        (groverParallelMarkingOracle m (insert x.1 K)))
      (programOf c (insert x.1 K)) Δ₀ =
      expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m (insert x.1 K)))
        (c.compile QProg.qAssign (groverParallelMarkingOracle m (insert x.1 K)))
        (CQState.qSet Δ₀) := by
    simp [programOf]
  rw [h4, htr] at h3
  have h5 := h1.trans (h2.trans h3)
  simp only [ENNReal.coe_one, one_mul] at h5
  have := (ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top).1 h5
  simpa using this

private lemma succR_eq (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m))
    (K : Finset (Fin (2 ^ n)))
    (σ₀ : Store Var) (x : RIdx n K) (Δ₀ : CQState (Store Var) (2 ^ Q))
    (hrep : Rep (CQState.qSet Δ₀) [(initBranch σ₀ : Branch Var (RIdx n K) Q)] x) (M : ℕ) :
    𝔼[(interp ((unroll M c).compile (groverParallelMarkingOracle m (insert x.1 K)))).toStateFun
        (CQState.qSet Δ₀) ⊨ fun σ ↦ ⌜decodeTargets n k (σ res) = insert x.1 K⌝] =
      succG (goodR n k K) x
        (ens (GR n m Q K) (unroll M c) [(initBranch σ₀ : Branch Var (RIdx n K) Q)]) := by
  have hR := rep_interp (i₀ := x) (groverParallelMarkingOracle m (insert x.1 K)) (GR n m Q K)
    (fun _ _ ↦ rfl) (unroll M c) hrep
  exact rep_post (fun σ : Store Var ↦ goodR n k K σ x) hR

end link

/-! ### The reveal floor -/

theorem reveal_core {n m k Q : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (K : Finset (Fin (2 ^ n))) (hK : K.card = k - 1)
    (hn : 4 * m ≤ 2 ^ n - (k - 1))
    (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m))
    (hmeets : MeetsFindAllSpec k c)
    (hfac : ∀ (r : QRegister ((n + 1) * m) Q) (x : Fin (2 ^ n)), x ∉ K →
      (r.embedUnitary (groverParallelMarkingOracle m (insert x K))).1 =
        (r.embedUnitary (groverParallelMarkingOracle m K)).1 *
          (r.embedUnitary (groverParallelMarkingOracle m {x})).1)
    (hsum : ∀ (r : QRegister ((n + 1) * m) Q) (u : Fin (2 ^ Q) → ℂ),
      ∑ x : Fin (2 ^ n), nsq ((r.embedUnitary (groverParallelMarkingOracle m {x})).1 *ᵥ u - u) ≤
        4 * (m : ℝ) * nsq u)
    (q : Finset (Fin (2 ^ n)) → ℝ≥0)
    (hq : ∀ S ∈ groverTargetSets n k,
      CostBound (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S)) (programOf c S) (q S)) :
    (π / 8 + 1 / 4) * √(((2 ^ n - (k - 1) : ℕ) : ℝ) / m) - 4 / √(((2 ^ n - (k - 1) : ℕ) : ℝ) / m) ≤
      (∑ x ∈ Finset.univ.filter (fun x => x ∉ K), (q (insert x K) : ℝ)) / ((2 ^ n - (k - 1) : ℕ) : ℝ) := by
  classical
  have hcardι : Fintype.card (RIdx n K) = 2 ^ n - (k - 1) := by rw [card_RIdx, hK]
  have hNpos' : 0 < 2 ^ n - (k - 1) := by omega
  haveI : Nonempty (RIdx n K) := Fintype.card_pos_iff.1 (by rw [hcardι]; exact hNpos')
  -- numbers
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hNpos : (0 : ℝ) < ((2 ^ n - (k - 1) : ℕ) : ℝ) := by exact_mod_cast hNpos'
  have h4 : (4 : ℝ) * m ≤ ((2 ^ n - (k - 1) : ℕ) : ℝ) := by exact_mod_cast hn
  set t : ℝ := √(((2 ^ n - (k - 1) : ℕ) : ℝ) / m) with htdef
  have htsq : t ^ 2 = ((2 ^ n - (k - 1) : ℕ) : ℝ) / m := Real.sq_sqrt (by positivity)
  have htB : t ^ 2 = (Fintype.card (RIdx n K) : ℝ) / (m : ℝ) := by rw [htsq, hcardι]
  have ht2 : (2 : ℝ) ≤ t := by
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hm0]
    linarith
  -- the end-bound ratio
  have hkey : 2 * ((1 : ℕ) : ℝ) / (Fintype.card (RIdx n K) : ℝ) ≤ 2 / t ^ 2 := by
    rw [htsq, hcardι, div_div_eq_mul_div, div_le_div_iff₀ hNpos hNpos]
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.2 hmr) hNpos.le]
  -- oracle facts
  have hG : ∀ (x : RIdx n K) (i : ℕ) (r : QRegister ((n + 1) * m) Q),
      GR n m Q K x i r = (WR n m Q K i r).1 * GR1 n m Q K x i r :=
    fun x _ r ↦ hfac r x.1 x.2
  have hsa : ∀ (x : RIdx n K) (i : ℕ) (r : QRegister ((n + 1) * m) Q),
      (GR1 n m Q K x i r).conjTranspose = GR1 n m Q K x i r :=
    fun x _ r ↦ parallelOracle_selfAdjoint r {x.1}
  have hinv : ∀ (x : RIdx n K) (i : ℕ) (r : QRegister ((n + 1) * m) Q),
      GR1 n m Q K x i r * GR1 n m Q K x i r = 1 :=
    fun x _ r ↦ parallelOracle_mul_self r {x.1}
  have hF2 : ∀ (i : ℕ) (r : QRegister ((n + 1) * m) Q) (u : Fin (2 ^ Q) → ℂ),
      ∑ x : RIdx n K, nsq (GR1 n m Q K x i r *ᵥ u - u) ≤ 4 * (m : ℝ) * nsq u := by
    intro i r u
    have e := sum_RIdx K
      (fun x ↦ nsq ((r.embedUnitary (groverParallelMarkingOracle m {x})).1 *ᵥ u - u))
    calc ∑ x : RIdx n K, nsq (GR1 n m Q K x i r *ᵥ u - u)
        = ∑ x ∈ Finset.univ.filter (fun x : Fin (2 ^ n) ↦ x ∉ K),
            nsq ((r.embedUnitary (groverParallelMarkingOracle m {x})).1 *ᵥ u - u) := e
      _ ≤ ∑ x : Fin (2 ^ n), nsq ((r.embedUnitary (groverParallelMarkingOracle m {x})).1 *ᵥ u - u) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ ↦ nsq_nonneg _)
      _ ≤ 4 * (m : ℝ) * nsq u := hsum r u
  -- costs
  set Bq : ℝ := ∑ x ∈ Finset.univ.filter (fun x : Fin (2 ^ n) ↦ x ∉ K),
    (q (insert x K) : ℝ) with hBq
  have hsumq : ∑ x : RIdx n K, (q (insert x.1 K) : ℝ) = Bq :=
    sum_RIdx K (fun x ↦ (q (insert x K) : ℝ))
  obtain ⟨bound, hbdef⟩ : ∃ b : ℝ, b = Bq / ((2 ^ n - (k - 1) : ℕ) : ℝ) := ⟨_, rfl⟩
  -- runs
  have hg0 : (0 : ℝ) ≤ π / 8 + 1 / 4 := by positivity
  set κ : ℝ := 2 / Real.arcsin (2 / t) with hκdef
  have hκ : 0 < κ := GroverThreeFifths.kappa_pos t ht2
  let σ₀ : Store Var := fun _ ↦ 0
  choose Δ₀ htr hrep using
    fun x : RIdx n K ↦ exists_init (ι := RIdx n K) (Q := Q) (i₀ := x) σ₀
  let Ψ : RIdx n K → CQAssertion (Store Var) (2 ^ Q) :=
    fun x σ ↦ ⌜decodeTargets n k (σ res) = insert x.1 K⌝
  let s : ℕ → RIdx n K → ℝ := fun M x ↦
    𝔼[(interp ((unroll M c).compile (groverParallelMarkingOracle m (insert x.1 K)))).toStateFun
      (CQState.qSet (Δ₀ x)) ⊨ Ψ x]
  let Lx : RIdx n K → ℝ := fun x ↦
    𝔼[(interp (c.compile QProg.qAssign (groverParallelMarkingOracle m (insert x.1 K)))).toStateFun
      (CQState.qSet (Δ₀ x)) ⊨ Ψ x]
  have hL : ∀ x, 1 ≤ Lx x := by
    intro x
    have h0 := hmeets (insert x.1 K) (insert_mem_targets hk K hK x) (Δ₀ x)
    rw [expect_programOf, expect_top, htr] at h0
    exact_mod_cast h0
  let init : List (Branch Var (RIdx n K) Q) := [initBranch σ₀]
  -- the inequality for every unrolling depth
  have hM : ∀ M : ℕ, κ * (π / 8 + 1 / 4) ≤
      κ * (π / 8 + 1 / 4) * (2 * ((1 : ℕ) : ℝ) / (Fintype.card (RIdx n K) : ℝ) +
        2 / (Fintype.card (RIdx n K) : ℝ) * ∑ x, (1 - s M x)) + bound := by
    intro M
    set E := ens (GR n m Q K) (unroll M c) init with hE
    have h1 := pwS_ens_mono_W (GR n m Q K) (GR1 n m Q K) (WR n m Q K) hG hsa hinv (m : ℝ) hm0
      hF2 t htB ht2 (unroll M c) init
    have h2 : κ * (π / 8 + 1 / 4) ≤ (init.map (pwS κ GroverThreeFifths.Vf)).sum := by
      have : (init.map (pwS κ GroverThreeFifths.Vf)).sum = κ * GroverThreeFifths.Vf 1 1 := by
        simp only [init, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        exact start_pwS κ σ₀
      rw [this, GroverThreeFifths.Vf_self 1 zero_le_one, mul_one]
    have h3 := end_pwS κ hκ.le E
    have hmass : ∀ x, (E.map fun β ↦ nsq (β.vec x)).sum ≤ 1 := by
      intro x
      have h := GroverThreeFifths.mass_ens_le (GR n m Q K) (fun i _ r v ↦ nsq_unitary _ v) (unroll M c) init x
      have h' : (init.map fun β ↦ nsq (β.vec x)).sum = 1 := by
        simp only [init, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        exact nsq_init Q
      linarith
    have h4 := sum_meanS_le (goodR n k K) 1 (card_goodR_le K) E hmass
    have hs : ∀ x, s M x = succG (goodR n k K) x E := fun x ↦ succR_eq c K σ₀ x (Δ₀ x) (hrep x) M
    have h5 : ∑ x, (1 - succG (goodR n k K) x E) = ∑ x, (1 - s M x) :=
      Finset.sum_congr rfl fun x _ ↦ by rw [hs x]
    rw [h5] at h4
    have h6 : ∑ x, GroverThreeFifths.cwa x E ≤ ∑ x : RIdx n K, (q (insert x.1 K) : ℝ) :=
      Finset.sum_le_sum fun x _ ↦
        cwaR_le c K σ₀ x (Δ₀ x) (htr x) (hrep x) (q (insert x.1 K))
          (hq _ (insert_mem_targets hk K hK x)) M
    have h7 := cwaS_sum E
    rw [hsumq] at h6
    have h8 : (E.map fun β ↦ (β.count : ℝ) * avgS β.vec).sum ≤ bound := by
      rw [hbdef, le_div_iff₀ hNpos, ← hcardι]
      rw [mul_comm, ← h7]
      exact h6
    have h9 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ κ * (π / 8 + 1 / 4))
    linarith
  -- let the depth go to infinity
  have hlim : Tendsto (fun M ↦ ∑ x, (1 - s M x)) atTop (nhds (∑ x, (1 - Lx x))) := by
    refine tendsto_finset_sum _ fun x _ ↦ ?_
    exact tendsto_const_nhds.sub
      (unroll_expect_tendsto (groverParallelMarkingOracle m (insert x.1 K)) c
        (CQState.qSet (Δ₀ x)) (Ψ x))
  set β : ℝ := κ * (π / 8 + 1 / 4) *
    (2 * ((1 : ℕ) : ℝ) / (Fintype.card (RIdx n K) : ℝ)) with hβ
  set γ : ℝ := κ * (π / 8 + 1 / 4) * (2 / (Fintype.card (RIdx n K) : ℝ)) with hγ
  have hγ0 : 0 ≤ γ := by positivity
  have hlim2 := hlim.const_mul γ
  have hge : κ * (π / 8 + 1 / 4) - β - bound ≤ γ * ∑ x, (1 - Lx x) := by
    refine ge_of_tendsto' hlim2 fun M ↦ ?_
    have := hM M
    have e : κ * (π / 8 + 1 / 4) * (2 * ((1 : ℕ) : ℝ) / (Fintype.card (RIdx n K) : ℝ) +
        2 / (Fintype.card (RIdx n K) : ℝ) * ∑ x, (1 - s M x)) =
        β + γ * ∑ x, (1 - s M x) := by rw [hβ, hγ]; ring
    linarith
  have hneg : ∑ x, (1 - Lx x) ≤ 0 :=
    Finset.sum_nonpos fun x _ ↦ by linarith [hL x]
  have hz : γ * ∑ x, (1 - Lx x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hγ0 hneg
  have hκc : 0 ≤ κ * (π / 8 + 1 / 4) := by positivity
  have hcmp := mul_le_mul_of_nonneg_left hkey hκc
  have hfin : κ * ((π / 8 + 1 / 4) * (1 - 2 / t ^ 2)) ≤ bound := by
    have e1 : κ * ((π / 8 + 1 / 4) * (1 - 2 / t ^ 2)) =
        κ * (π / 8 + 1 / 4) - κ * (π / 8 + 1 / 4) * (2 / t ^ 2) := by ring
    rw [e1]
    linarith
  have hend := GroverThreeFifths.kappa_end t ht2
  rw [← hbdef]
  linarith

end GroverParallel

#print axioms GroverParallel.reveal_core
