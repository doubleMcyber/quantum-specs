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
import LowerBounds.Grover.FindAllFloorEnd
import LowerBounds.Grover.FindAllOracle
import LowerBounds.Grover.ParallelBound
import LowerBounds.Grover.ParallelCost
import Mathlib

/-!
# The find-all floor from a potential, `m` slots

`fa_floor_core_m`: the statement of `fa_floor_core` for a circuit with `m` slots, with the oracle
hypothesis given directly as the drop bound `hH` for Google's marking oracle with `m` slots.
-/

open QuantumComputation.Specs Operator ResourceCounting Filter Real
open scoped Matrix QHLExpectation ComplexOrder MatrixOrder ENNReal NNReal
open QuantumComputation.Specs.Grover (Var)
open QuantumComputation.Specs.Grover.Var (res)

namespace GroverParallel

open GroverLowerBound

private lemma list_add_m {α : Type} (E : List α) (f g : α → ℝ) :
    (E.map fun a ↦ f a + g a).sum = (E.map f).sum + (E.map g).sum := by
  induction E with
  | nil => simp
  | cons b E ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

private lemma list_mul_left_m {α : Type} (E : List α) (f : α → ℝ) (c : ℝ) :
    (E.map fun a ↦ c * f a).sum = c * (E.map f).sum := by
  induction E with
  | nil => simp
  | cons b E ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]

theorem fa_floor_core_m {n m k Q : ℕ} (hk : 1 ≤ k) (hkN : k ≤ 2 ^ n)
    (c : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m))
    (hmeets : MeetsFindAllSpec k c)
    (Y : KSet n k → KSet n k → ℝ)
    (hH : ∀ (i : ℕ) (r : QRegister ((n + 1) * m) Q) (v : KSet n k → Fin (2 ^ Q) → ℂ),
      gramY Y v - gramY Y (fun S => GK n m k Q S i r *ᵥ v S) ≤ ∑ S, nsq (v S))
    (hdiag : ∀ S, Y S S ≤ 0)
    (bound : ℝ)
    (hbound : AvgOracleCostBound k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦ programOf c S) bound) :
    ∑ S, ∑ S', Y S S' ≤ ((2 ^ n).choose k : ℝ) * bound := by
  classical
  obtain ⟨q, hq, havg⟩ := hbound
  haveI : Nonempty (KSet n k) := kset_nonempty hkN
  have hcardK := card_KSet n k
  have hBpos : 0 < (2 ^ n).choose k := Nat.choose_pos hkN
  have hBr : (0 : ℝ) < ((2 ^ n).choose k : ℕ) := by exact_mod_cast hBpos
  obtain ⟨Ymax, hYmax⟩ : ∃ Ymax : ℝ, ∀ S S', |Y S S'| ≤ Ymax :=
    ⟨∑ S, ∑ S', |Y S S'|, fun S S' => by
      calc |Y S S'| ≤ ∑ S'', |Y S S''| :=
            Finset.single_le_sum (f := fun S'' => |Y S S''|) (fun _ _ => abs_nonneg _)
              (Finset.mem_univ S')
        _ ≤ ∑ T, ∑ S'', |Y T S''| :=
            Finset.single_le_sum (f := fun T => ∑ S'', |Y T S''|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ S)⟩
  -- oracle facts
  have hsa : ∀ (S : KSet n k) (i : ℕ) (r : QRegister ((n + 1) * m) Q),
      (GK n m k Q S i r).conjTranspose = GK n m k Q S i r :=
    fun S _ r ↦ parallelOracle_selfAdjoint r S.1
  have hinv : ∀ (S : KSet n k) (i : ℕ) (r : QRegister ((n + 1) * m) Q),
      GK n m k Q S i r * GK n m k Q S i r = 1 :=
    fun S _ r ↦ parallelOracle_mul_self r S.1
  -- costs
  have hsumT : ∑ S ∈ groverTargetSets n k, (q S : ℝ) ≤ ((2 ^ n).choose k : ℕ) * bound := by
    rw [card_targetSets, div_le_iff₀ hBr] at havg
    linarith
  have hsumK : ∑ S : KSet n k, (q S.1 : ℝ) = ∑ S ∈ groverTargetSets n k, (q S : ℝ) :=
    sum_KSet (fun S ↦ (q S : ℝ))
  have hsuc1 : ∀ (S : KSet n k) (Δ : CQState (Store Var) (2 ^ Q)), Δ.trace = 1 →
      (1 : ℝ) ≤ 𝔼[(interp (c.compile QProg.qAssign
        (groverParallelMarkingOracle m S.1))).toStateFun (CQState.qSet Δ) ⊨
          (fun σ ↦ ⌜decodeTargets n k (σ res) = S.1⌝)] := by
    intro S Δ htr
    have h0 := hmeets S.1 S.2 Δ
    rw [expect_programOf, expect_top, htr] at h0
    exact_mod_cast h0
  -- runs
  let σ₀ : Store Var := fun _ ↦ 0
  choose Δ₀ htr hrep using
    fun S : KSet n k ↦ exists_init (ι := KSet n k) (Q := Q) (i₀ := S) σ₀
  let s : ℕ → KSet n k → ℝ := fun M S ↦
    𝔼[(interp ((unroll M c).compile (groverParallelMarkingOracle m S.1))).toStateFun
      (CQState.qSet (Δ₀ S)) ⊨ (fun σ ↦ ⌜decodeTargets n k (σ res) = S.1⌝)]
  let Lx : KSet n k → ℝ := fun S ↦
    𝔼[(interp (c.compile QProg.qAssign (groverParallelMarkingOracle m S.1))).toStateFun
      (CQState.qSet (Δ₀ S)) ⊨ (fun σ ↦ ⌜decodeTargets n k (σ res) = S.1⌝)]
  have hL : ∀ S, 1 ≤ Lx S := fun S ↦ hsuc1 S (Δ₀ S) (htr S)
  let init : List (Branch Var (KSet n k) Q) := [initBranch σ₀]
  have hs : ∀ (M : ℕ) (S : KSet n k),
      s M S = succG (goodAll n k) S (ens (GK n m k Q) (unroll M c) init) :=
    fun M S ↦ succAll_eq c σ₀ S (Δ₀ S) (hrep S) M
  have hmassM : ∀ (M : ℕ) (S : KSet n k),
      ((ens (GK n m k Q) (unroll M c) init).map fun β ↦ nsq (β.vec S)).sum ≤ 1 := by
    intro M S
    have h := GroverThreeFifths.mass_ens_le (GK n m k Q) (fun i _ r v ↦ nsq_unitary _ v) (unroll M c) init S
    have h' : (init.map fun β ↦ nsq (β.vec S)).sum = 1 := by
      simp only [init, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact nsq_init Q
    linarith
  have hsle : ∀ (M : ℕ) (S : KSet n k), s M S ≤ 1 := by
    intro M S
    rw [hs M S]
    refine le_trans ?_ (hmassM M S)
    unfold succG
    rw [sum_filter_ite]
    refine List.sum_le_sum fun β _ => ?_
    split_ifs
    · exact le_rfl
    · exact nsq_nonneg _
  -- the inequality for every unrolling depth
  have hM : ∀ M : ℕ, ∑ S, ∑ S', Y S S' ≤ ((2 ^ n).choose k : ℕ) * bound +
      Ymax * ((2 ^ n).choose k : ℕ) *
        (2 * √(∑ S, (1 - s M S)) + ∑ S, (1 - s M S)) := by
    intro M
    set E := ens (GK n m k Q) (unroll M c) init with hE
    have h1 : (init.map (pwY Y)).sum ≤ (E.map (pwY Y)).sum :=
      pwY_ens_mono (GK n m k Q) hsa hinv Y hH (unroll M c) init
    have h2 : (init.map (pwY Y)).sum = ∑ S, ∑ S', Y S S' := by
      have e : (initBranch σ₀ : Branch Var (KSet n k) Q).vec =
          fun _ => Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ) := rfl
      simp only [init, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      unfold pwY
      rw [e, gramY_init]
      simp [initBranch]
    have h3 : (E.map (pwY Y)).sum = (E.map fun β ↦ gramY Y β.vec).sum +
        (E.map fun β ↦ (β.count : ℝ) * ∑ S, nsq (β.vec S)).sum := by
      have e : E.map (pwY Y) = E.map fun β ↦
          gramY Y β.vec + (β.count : ℝ) * ∑ S, nsq (β.vec S) := rfl
      rw [e, list_add_m]
    have hmass : ∀ S, (E.map fun β ↦ nsq (β.vec S)).sum ≤ 1 := fun S ↦ hmassM M S
    have h5 := end_gramY_le Y hdiag Ymax hYmax (goodAll n k) card_goodAll_le E hmass
    have h5e : ∑ S, (1 - succG (goodAll n k) S E) = ∑ S, (1 - s M S) :=
      Finset.sum_congr rfl fun S _ ↦ by rw [hs M S]
    rw [h5e, hcardK] at h5
    have h6 : ∑ S, GroverThreeFifths.cwa S E ≤ ∑ S : KSet n k, (q S.1 : ℝ) :=
      Finset.sum_le_sum fun S _ ↦
        cwaK_le c σ₀ S (Δ₀ S) (htr S) (hrep S) (q S.1) (hq S.1 S.2) M
    have h7 := cwaS_sum E
    have hN : (Fintype.card (KSet n k) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have hcnt : (E.map fun β ↦ (β.count : ℝ) * ∑ S, nsq (β.vec S)).sum =
        ∑ S, GroverThreeFifths.cwa S E := by
      rw [h7, ← list_mul_left_m]
      refine congrArg List.sum (List.map_congr_left fun β _ => ?_)
      unfold avgS
      field_simp
    linarith
  -- let the depth go to infinity
  have hlim : Tendsto (fun M ↦ ∑ S, (1 - s M S)) atTop (nhds (∑ S, (1 - Lx S))) := by
    refine tendsto_finset_sum _ fun S _ ↦ ?_
    exact tendsto_const_nhds.sub
      (unroll_expect_tendsto (groverParallelMarkingOracle m S.1) c (CQState.qSet (Δ₀ S))
        (fun σ ↦ ⌜decodeTargets n k (σ res) = S.1⌝))
  have hε0 : 0 ≤ ∑ S, (1 - Lx S) :=
    ge_of_tendsto' hlim fun M ↦ Finset.sum_nonneg fun S _ ↦ by linarith [hsle M S]
  have hε1 : ∑ S, (1 - Lx S) ≤ 0 := Finset.sum_nonpos fun S _ ↦ by linarith [hL S]
  have hz : ∑ S, (1 - Lx S) = 0 := le_antisymm hε1 hε0
  have hsq := (Real.continuous_sqrt.tendsto _).comp hlim
  have hlim2 : Tendsto (fun M ↦ ((2 ^ n).choose k : ℕ) * bound +
      Ymax * ((2 ^ n).choose k : ℕ) * (2 * √(∑ S, (1 - s M S)) + ∑ S, (1 - s M S)))
      atTop (nhds (((2 ^ n).choose k : ℕ) * bound +
      Ymax * ((2 ^ n).choose k : ℕ) * (2 * √(∑ S, (1 - Lx S)) + ∑ S, (1 - Lx S)))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul ((tendsto_const_nhds.mul hsq).add hlim))
  have hfin := ge_of_tendsto' hlim2 hM
  rw [hz] at hfin
  simpa using hfin

end GroverParallel

#print axioms GroverParallel.fa_floor_core_m
