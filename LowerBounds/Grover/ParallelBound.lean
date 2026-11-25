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
import LowerBounds.Grover.ParallelWeight
import LowerBounds.Grover.ParallelCost
import LowerBounds.Grover.ParallelLink
import LowerBounds.Grover.ParallelOracle
import LowerBounds.Grover.ParallelFullStatement
import LowerBounds.Grover.FullBound
import Mathlib

/-!
# The lower bounds at every cell `(m, k)`

* `GroverParallel.fullTargetAny m k : FullTargetAny m k` and
  `GroverParallel.fullTargetAll m k : FullTargetAll m k`, for all `m, k ≥ 1`: every circuit meeting
  the find-any (respectively find-all) correctness statement at cell `(m, k)` has
  `(π / 8 + 1 / 4) t - 4 / t ≤ bound` with `t = √(2 ^ n / (m k))`, for every
  `n ≥ 2 + Nat.clog 2 (m * k)`.
* `GroverParallel.findAny_35`, `GroverParallel.findAll_35`: the constant `3 / 5` with no error term
  for `n ≥ 16 + Nat.clog 2 (m * k)`, where `t ≥ 256`.

The assembly is that of `GroverThreeFifths.findAny_lower_bound_full` (`FullBound.lean`) with run
index `KSet n k`, `B = C(2^n, k)` runs and oracle footprint `L = m C(2^n - 1, k - 1)`
(`parallelOracle_sq_sum_le`), so that `t² = B / L = 2^n / (m k)` (`choose_mul_two_pow`). At the end
at most `κe` runs succeed per store, with `κe = C(2^n - 1, k - 1)` for find-any and `κe = 1` for
find-all. In both cases `κe 2^n ≤ k B`, and `GroverThreeFifths.kappa_end` closes the bound.
`bound_core` takes the success predicate and the two link facts as hypotheses.
-/

open QuantumComputation.Specs Operator ResourceCounting Filter Real
open scoped Matrix QHLExpectation ComplexOrder MatrixOrder ENNReal NNReal
open QuantumComputation.Specs.Grover (Var)
open QuantumComputation.Specs.Grover.Var (res)

namespace GroverParallel

open GroverLowerBound

/-! ### Start and end of the potential -/

section ends

variable {ι : Type} [Fintype ι] [Nonempty ι] {Q : ℕ}

lemma start_pwS (κ : ℝ) (σ₀ : Store Var) :
    pwS κ GroverThreeFifths.Vf (initBranch σ₀ : Branch Var ι Q) = κ * GroverThreeFifths.Vf 1 1 := by
  have e : (initBranch σ₀ : Branch Var ι Q).vec =
      fun _ => Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ) := rfl
  unfold pwS
  rw [e, meanS_const, avgS_const, nsq_init]
  simp [initBranch]

lemma end_pwS (κ : ℝ) (hκ : 0 ≤ κ) (E : List (Branch Var ι Q)) :
    (E.map (pwS κ GroverThreeFifths.Vf)).sum ≤
      κ * (π / 8 + 1 / 4) * (E.map fun β ↦ nsq (meanS β.vec)).sum +
        (E.map fun β ↦ (β.count : ℝ) * avgS β.vec).sum := by
  have h : (E.map (pwS κ GroverThreeFifths.Vf)).sum ≤
      (E.map fun β ↦ (κ * (π / 8 + 1 / 4)) * nsq (meanS β.vec)
        + (β.count : ℝ) * avgS β.vec).sum := by
    refine List.sum_le_sum fun β _ => ?_
    unfold pwS
    have := GroverThreeFifths.Vf_le (nsq (meanS β.vec)) (avgS β.vec) (nsq_nonneg _) (nsq_meanS_le _)
    have := mul_le_mul_of_nonneg_left this hκ
    linarith
  rw [GroverThreeFifths.list_lin] at h
  exact h

end ends

/-! ### Counting -/

lemma card_KSet (n k : ℕ) : Fintype.card (KSet n k) = (2 ^ n).choose k := by
  simp [KSet, groverTargetSets, Finset.card_powersetCard]

lemma card_targetSets (n k : ℕ) : (groverTargetSets n k).card = (2 ^ n).choose k := by
  simp [groverTargetSets, Finset.card_powersetCard]

lemma kset_nonempty {n k : ℕ} (hk : k ≤ 2 ^ n) : Nonempty (KSet n k) := by
  have h : (groverTargetSets n k).Nonempty := by
    simp [groverTargetSets, Finset.powersetCard_nonempty, hk]
  obtain ⟨S, hS⟩ := h
  exact ⟨⟨S, hS⟩⟩

lemma sum_KSet {n k : ℕ} (f : Finset (Fin (2 ^ n)) → ℝ) :
    ∑ S : KSet n k, f S.1 = ∑ S ∈ groverTargetSets n k, f S :=
  (Finset.sum_subtype _ (fun _ => Iff.rfl) f).symm

/-! ### The assembly at cell (m, k), for any success predicate -/

theorem bound_core {n m k Q : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (hn : 4 * (m * k) ≤ 2 ^ n)
    (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m))
    (good : Store Var → KSet n k → Prop) [∀ σ S, Decidable (good σ S)]
    (κe : ℕ) (hκe : ∀ σ, (Finset.univ.filter (good σ)).card ≤ κe)
    (hκeN : κe * 2 ^ n ≤ k * (2 ^ n).choose k)
    (Ψ : KSet n k → CQAssertion (Store Var) (2 ^ Q))
    (hsucc : ∀ (σ₀ : Store Var) (S : KSet n k) (Δ₀ : CQState (Store Var) (2 ^ Q)),
      Rep (CQState.qSet Δ₀) [(initBranch σ₀ : Branch Var (KSet n k) Q)] S → ∀ M : ℕ,
      𝔼[(interp ((unroll M c).compile (groverParallelMarkingOracle m S.1))).toStateFun
          (CQState.qSet Δ₀) ⊨ Ψ S] =
        succG good S (ens (GK n m k Q) (unroll M c) [(initBranch σ₀ : Branch Var (KSet n k) Q)]))
    (hsuc1 : ∀ (S : KSet n k) (Δ : CQState (Store Var) (2 ^ Q)), Δ.trace = 1 →
      (1 : ℝ) ≤ 𝔼[(interp (c.compile QProg.qAssign (groverParallelMarkingOracle m S.1))).toStateFun
          (CQState.qSet Δ) ⊨ Ψ S])
    (bound : ℝ)
    (hbound : AvgOracleCostBound k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦ programOf c S) bound) :
    (π / 8 + 1 / 4) * √((2 : ℝ) ^ n / ((m : ℝ) * k)) - errMK m k n ≤ bound := by
  classical
  obtain ⟨q, hq, havg⟩ := hbound
  have hkN : k ≤ 2 ^ n := le_trans (by nlinarith) hn
  haveI : Nonempty (KSet n k) := kset_nonempty hkN
  have hcardK := card_KSet n k
  have hchoose : (2 ^ n - 1).choose (k - 1) * 2 ^ n = k * (2 ^ n).choose k := choose_mul_two_pow hk
  have hBpos : 0 < (2 ^ n).choose k := Nat.choose_pos hkN
  have hLcpos : 0 < (2 ^ n - 1).choose (k - 1) := Nat.choose_pos (Nat.sub_le_sub_right hkN 1)
  -- numbers
  have hBr : (0 : ℝ) < ((2 ^ n).choose k : ℕ) := by exact_mod_cast hBpos
  have hNpos : (0 : ℝ) < 2 ^ n := by positivity
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hmk : (0 : ℝ) < (m : ℝ) * k := mul_pos (by linarith) (by linarith)
  set Lr : ℝ := (m : ℝ) * (((2 ^ n - 1).choose (k - 1) : ℕ) : ℝ) with hLr
  have hLpos : 0 < Lr := mul_pos (by linarith) (by exact_mod_cast hLcpos)
  set t : ℝ := √((2 : ℝ) ^ n / ((m : ℝ) * k)) with htdef
  have htsq : t ^ 2 = 2 ^ n / ((m : ℝ) * k) := Real.sq_sqrt (by positivity)
  have hchr : (((2 ^ n - 1).choose (k - 1) : ℕ) : ℝ) * 2 ^ n = k * ((2 ^ n).choose k : ℕ) := by
    exact_mod_cast hchoose
  have htB : t ^ 2 = (Fintype.card (KSet n k) : ℝ) / Lr := by
    rw [htsq, hcardK, hLr, div_eq_div_iff hmk.ne' (by positivity)]
    linear_combination (m : ℝ) * hchr
  have h4 : (4 : ℝ) * ((m : ℝ) * k) ≤ 2 ^ n := by exact_mod_cast hn
  have ht2 : (2 : ℝ) ≤ t := by
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hmk]
    linarith
  -- the end-bound ratio
  have hkey : 2 * (κe : ℝ) / ((2 ^ n).choose k : ℕ) ≤ 2 / t ^ 2 := by
    rw [htsq, div_div_eq_mul_div, div_le_div_iff₀ hBr hNpos]
    have h0 : (κe : ℝ) * 2 ^ n ≤ k * ((2 ^ n).choose k : ℕ) := by exact_mod_cast hκeN
    nlinarith [mul_nonneg (sub_nonneg.2 hmr) (by positivity : (0 : ℝ) ≤ k * ((2 ^ n).choose k : ℕ))]
  -- oracle facts
  have hsa : ∀ (S : KSet n k) (i : ℕ) (r : QRegister ((n + 1) * m) Q),
      (GK n m k Q S i r).conjTranspose = GK n m k Q S i r :=
    fun S _ r ↦ parallelOracle_selfAdjoint r S.1
  have hinv : ∀ (S : KSet n k) (i : ℕ) (r : QRegister ((n + 1) * m) Q),
      GK n m k Q S i r * GK n m k Q S i r = 1 :=
    fun S _ r ↦ parallelOracle_mul_self r S.1
  have hF2 : ∀ (i : ℕ) (r : QRegister ((n + 1) * m) Q) (u : Fin (2 ^ Q) → ℂ),
      ∑ S : KSet n k, nsq (GK n m k Q S i r *ᵥ u - u) ≤ 4 * Lr * nsq u := by
    intro i r u
    have h := parallelOracle_sq_sum_le (m := m) k hk r u
    calc ∑ S : KSet n k, nsq (GK n m k Q S i r *ᵥ u - u)
        = ∑ S ∈ groverTargetSets n k,
            nsq ((r.embedUnitary (groverParallelMarkingOracle m S)).1 *ᵥ u - u) :=
          sum_KSet (fun S ↦ nsq ((r.embedUnitary (groverParallelMarkingOracle m S)).1 *ᵥ u - u))
      _ ≤ 4 * Lr * nsq u := h
  -- costs
  have hsumT : ∑ S ∈ groverTargetSets n k, (q S : ℝ) ≤ ((2 ^ n).choose k : ℕ) * bound := by
    rw [card_targetSets, div_le_iff₀ hBr] at havg
    linarith
  have hsumK : ∑ S : KSet n k, (q S.1 : ℝ) = ∑ S ∈ groverTargetSets n k, (q S : ℝ) :=
    sum_KSet (fun S ↦ (q S : ℝ))
  -- runs
  have hg0 : (0 : ℝ) ≤ π / 8 + 1 / 4 := by positivity
  set κ : ℝ := 2 / Real.arcsin (2 / t) with hκdef
  have hκ : 0 < κ := GroverThreeFifths.kappa_pos t ht2
  let σ₀ : Store Var := fun _ ↦ 0
  choose Δ₀ htr hrep using
    fun S : KSet n k ↦ exists_init (ι := KSet n k) (Q := Q) (i₀ := S) σ₀
  let s : ℕ → KSet n k → ℝ := fun M S ↦
    𝔼[(interp ((unroll M c).compile (groverParallelMarkingOracle m S.1))).toStateFun
      (CQState.qSet (Δ₀ S)) ⊨ Ψ S]
  let Lx : KSet n k → ℝ := fun S ↦
    𝔼[(interp (c.compile QProg.qAssign (groverParallelMarkingOracle m S.1))).toStateFun
      (CQState.qSet (Δ₀ S)) ⊨ Ψ S]
  have hL : ∀ S, 1 ≤ Lx S := fun S ↦ hsuc1 S (Δ₀ S) (htr S)
  let init : List (Branch Var (KSet n k) Q) := [initBranch σ₀]
  -- the inequality for every unrolling depth
  have hM : ∀ M : ℕ, κ * (π / 8 + 1 / 4) ≤
      κ * (π / 8 + 1 / 4) * (2 * (κe : ℝ) / ((2 ^ n).choose k : ℕ) +
        2 / (((2 ^ n).choose k : ℕ) : ℝ) * ∑ S, (1 - s M S)) + bound := by
    intro M
    set E := ens (GK n m k Q) (unroll M c) init with hE
    have h1 := pwS_ens_mono_full (GK n m k Q) hsa hinv Lr hLpos hF2 t htB ht2 (unroll M c) init
    have h2 : κ * (π / 8 + 1 / 4) ≤ (init.map (pwS κ GroverThreeFifths.Vf)).sum := by
      have : (init.map (pwS κ GroverThreeFifths.Vf)).sum = κ * GroverThreeFifths.Vf 1 1 := by
        simp only [init, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        exact start_pwS κ σ₀
      rw [this, GroverThreeFifths.Vf_self 1 zero_le_one, mul_one]
    have h3 := end_pwS κ hκ.le E
    have hmass : ∀ S, (E.map fun β ↦ nsq (β.vec S)).sum ≤ 1 := by
      intro S
      have h := GroverThreeFifths.mass_ens_le (GK n m k Q) (fun i _ r v ↦ nsq_unitary _ v) (unroll M c) init S
      have h' : (init.map fun β ↦ nsq (β.vec S)).sum = 1 := by
        simp only [init, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        exact nsq_init Q
      linarith
    have h4 := sum_meanS_le good κe hκe E hmass
    have hs : ∀ S, s M S = succG good S E := fun S ↦ hsucc σ₀ S (Δ₀ S) (hrep S) M
    have h5 : ∑ S, (1 - succG good S E) = ∑ S, (1 - s M S) :=
      Finset.sum_congr rfl fun S _ ↦ by rw [hs S]
    rw [h5, hcardK] at h4
    have h6 : ∑ S, GroverThreeFifths.cwa S E ≤ ∑ S : KSet n k, (q S.1 : ℝ) :=
      Finset.sum_le_sum fun S _ ↦
        cwaK_le c σ₀ S (Δ₀ S) (htr S) (hrep S) (q S.1) (hq S.1 S.2) M
    have h7 := cwaS_sum E
    rw [hcardK] at h7
    have h8 : (E.map fun β ↦ (β.count : ℝ) * avgS β.vec).sum ≤ bound := by
      have : (((2 ^ n).choose k : ℕ) : ℝ) * (E.map fun β ↦ (β.count : ℝ) * avgS β.vec).sum ≤
          ((2 ^ n).choose k : ℕ) * bound := by
        rw [← h7]
        linarith
      exact le_of_mul_le_mul_left this hBr
    have h9 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ κ * (π / 8 + 1 / 4))
    linarith
  -- let the depth go to infinity
  have hlim : Tendsto (fun M ↦ ∑ S, (1 - s M S)) atTop (nhds (∑ S, (1 - Lx S))) := by
    refine tendsto_finset_sum _ fun S _ ↦ ?_
    exact tendsto_const_nhds.sub
      (unroll_expect_tendsto (groverParallelMarkingOracle m S.1) c (CQState.qSet (Δ₀ S)) (Ψ S))
  set β : ℝ := κ * (π / 8 + 1 / 4) * (2 * (κe : ℝ) / ((2 ^ n).choose k : ℕ)) with hβ
  set γ : ℝ := κ * (π / 8 + 1 / 4) * (2 / (((2 ^ n).choose k : ℕ) : ℝ)) with hγ
  have hγ0 : 0 ≤ γ := by positivity
  have hlim2 := hlim.const_mul γ
  have hge : κ * (π / 8 + 1 / 4) - β - bound ≤ γ * ∑ S, (1 - Lx S) := by
    refine ge_of_tendsto' hlim2 fun M ↦ ?_
    have := hM M
    have e : κ * (π / 8 + 1 / 4) * (2 * (κe : ℝ) / ((2 ^ n).choose k : ℕ) +
        2 / (((2 ^ n).choose k : ℕ) : ℝ) * ∑ S, (1 - s M S)) =
        β + γ * ∑ S, (1 - s M S) := by rw [hβ, hγ]; ring
    linarith
  have hneg : ∑ S, (1 - Lx S) ≤ 0 :=
    Finset.sum_nonpos fun S _ ↦ by linarith [hL S]
  have hz : γ * ∑ S, (1 - Lx S) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hγ0 hneg
  have hκc : 0 ≤ κ * (π / 8 + 1 / 4) := by positivity
  have hcmp := mul_le_mul_of_nonneg_left hkey hκc
  have hfin : κ * ((π / 8 + 1 / 4) * (1 - 2 / t ^ 2)) ≤ bound := by
    have e1 : κ * ((π / 8 + 1 / 4) * (1 - 2 / t ^ 2)) =
        κ * (π / 8 + 1 / 4) - κ * (π / 8 + 1 / 4) * (2 / t ^ 2) := by ring
    rw [e1]
    linarith
  have hend := GroverThreeFifths.kappa_end t ht2
  show (π / 8 + 1 / 4) * t - 4 / t ≤ bound
  linarith

/-! ### The two targets -/

lemma k_le_of_n0full {m k n : ℕ} (hm : 1 ≤ m) (hn : n0full m k ≤ n) : k ≤ 2 ^ n :=
  le_trans (by nlinarith) (two_pow_n0full_ge m k n hn)

theorem fullTargetAny (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) : FullTargetAny m k := by
  intro n hn Q c hmeets bound hbound
  refine bound_core hm hk (two_pow_n0full_ge m k n hn) c (goodAny n k)
    ((2 ^ n - 1).choose (k - 1)) (card_goodAny_le hk) (choose_mul_two_pow hk).le
    (fun S ↦ fun σ ↦ ⌜∃ x ∈ S.1, σ res = x.val⌝)
    (fun σ₀ S Δ₀ hrep M ↦ succAny_eq c σ₀ S Δ₀ hrep M) ?_ bound hbound
  intro S Δ htr
  have h0 := hmeets S.1 S.2 Δ
  rw [expect_programOf, expect_top, htr] at h0
  exact_mod_cast h0

theorem fullTargetAll (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) : FullTargetAll m k := by
  intro n hn Q c hmeets bound hbound
  have hkN := k_le_of_n0full hm hn
  have hκeN : 1 * 2 ^ n ≤ k * (2 ^ n).choose k := by
    rw [← choose_mul_two_pow hk]
    exact Nat.mul_le_mul_right _ (Nat.choose_pos (Nat.sub_le_sub_right hkN 1))
  refine bound_core hm hk (two_pow_n0full_ge m k n hn) c (goodAll n k) 1
    card_goodAll_le hκeN
    (fun S ↦ fun σ ↦ ⌜decodeTargets n k (σ res) = S.1⌝)
    (fun σ₀ S Δ₀ hrep M ↦ succAll_eq c σ₀ S Δ₀ hrep M) ?_ bound hbound
  intro S Δ htr
  have h0 := hmeets S.1 S.2 Δ
  rw [expect_programOf, expect_top, htr] at h0
  exact_mod_cast h0

/-! ### The 3/5 versions at the original threshold -/

lemma t_ge_256 {m k n : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (hn : n0_of m k ≤ n) :
    (256 : ℝ) ≤ √((2 : ℝ) ^ n / ((m : ℝ) * k)) := by
  have hmk : (0 : ℝ) < (m : ℝ) * k := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    positivity
  have h16 : ((2 ^ 16 * (m * k) : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
    exact_mod_cast two_pow_n0_ge m k n hn
  push_cast at h16
  apply Real.le_sqrt_of_sq_le
  rw [le_div_iff₀ hmk]
  have e : (256 : ℝ) ^ 2 = 65536 := by norm_num
  rw [e]
  linarith

lemma n0full_le {m k n : ℕ} (hn : n0_of m k ≤ n) : n0full m k ≤ n := by
  unfold n0full; unfold n0_of at hn; omega

lemma three_fifths {t bound : ℝ} (ht : 256 ≤ t) (h : (π / 8 + 1 / 4) * t - 4 / t ≤ bound) :
    3 / 5 * t ≤ bound := by
  have hpt : 3 * t ≤ π * t := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (by linarith)
  have h4t : 4 / t ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  linarith

theorem findAny_35 (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    FindAnyLowerBoundMK m k (3 / 5) (n0_of m k) := by
  intro n hn Q c hmeets bound hbound
  exact three_fifths (t_ge_256 hm hk hn)
    (fullTargetAny m k hm hk n (n0full_le hn) Q c hmeets bound hbound)

theorem findAll_35 (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    FindAllLowerBoundMK m k (3 / 5) (n0_of m k) := by
  intro n hn Q c hmeets bound hbound
  exact three_fifths (t_ge_256 hm hk hn)
    (fullTargetAll m k hm hk n (n0full_le hn) Q c hmeets bound hbound)

end GroverParallel

#print axioms GroverParallel.fullTargetAny
#print axioms GroverParallel.fullTargetAll
#print axioms GroverParallel.findAny_35
#print axioms GroverParallel.findAll_35
