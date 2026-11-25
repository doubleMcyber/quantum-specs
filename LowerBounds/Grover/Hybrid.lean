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
import LowerBounds.Grover.OracleLocality
import Mathlib

/-!
# The hybrid argument on the branch semantics

The hybrid argument on `GroverLowerBound.ens hybridG`.

Main theorem `GroverLowerBound.hybrid_success_le`: summed over the marked item `x`, the weight of
the real run `(x, 0)` on live branches that passed at most `T` oracle nodes and whose store holds
`x` is at most `(2 T + 1) ^ 2`.

Route (all statements for every program and every input list, by induction on the program):
* `inv_ens`: invariant `Inv` (a branch with count `≤ l` has the same vector in run `(x, l)` as in
  the reference run `none`) is preserved.
* `rw0_ens`: the reference weight `∑ ‖β.vec none‖²` does not grow.
* `psi_mono`: the potential `psiB m` (a branch that passed its `(m+1)`-th oracle node contributes
  `4 ‖φ‖² - ∑ₓ ‖v(x,m) - v(x,m+1)‖²`) does not decrease; uses `oracle_sq_sum_le`.
* `gap_sum_le`: `∑_β ∑ₓ ‖v(x,m) - v(x,m+1)‖² ≤ 4` on the final list.
* Minkowski over the coordinates `(β, x, j)` for the two triangle inequalities.
-/

open QuantumComputation.Specs Operator
open scoped Matrix

namespace GroverLowerBound

/-! ### Linear algebra on coordinate vectors -/

lemma nsq_eq_dot {d : ℕ} (v : Fin d → ℂ) : nsq v = (star v ⬝ᵥ v).re := by
  simp [nsq, dotProduct, Complex.re_sum, Complex.normSq_apply]

lemma nsq_mulVec {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) :
    nsq (M *ᵥ v) = (star v ⬝ᵥ ((Mᴴ * M) *ᵥ v)).re := by
  rw [nsq_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

lemma nsq_unit {d : ℕ} (U : Unitary d) (v : Fin d → ℂ) : nsq (U.1 *ᵥ v) = nsq v := by
  have h : U.1ᴴ * U.1 = 1 := Unitary.star_mul_self_of_mem U.2
  rw [nsq_mulVec, h, Matrix.one_mulVec, nsq_eq_dot]

lemma nsq_mulVec_sub {d : ℕ} (U : Unitary d) (a b : Fin d → ℂ) :
    nsq (U.1 *ᵥ a - U.1 *ᵥ b) = nsq (a - b) := by
  rw [← Matrix.mulVec_sub, nsq_unit]

lemma sum_nsq_measure {d i : ℕ} (M : CompleteMeasurement d i) (v : Fin d → ℂ) :
    ∑ o, nsq (M.1 o *ᵥ v) = nsq v := by
  have h1 : ∀ o, nsq (M.1 o *ᵥ v) = (star v ⬝ᵥ (((M.1 o)ᴴ * M.1 o) *ᵥ v)).re :=
    fun o => nsq_mulVec _ _
  rw [Finset.sum_congr rfl fun o _ => h1 o, ← Complex.re_sum, ← dotProduct_sum,
    ← Matrix.sum_mulVec, M.2, Matrix.one_mulVec, nsq_eq_dot]

lemma nsq_init (Q : ℕ) : nsq (Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ)) = 1 := by
  unfold nsq
  rw [Finset.sum_eq_single (0 : Fin (2 ^ Q))]
  · simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma nsq_nonneg {d : ℕ} (v : Fin d → ℂ) : 0 ≤ nsq v :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-! ### List sums -/

lemma sum_finRange_map {α : Type} (k : ℕ) (g : Fin k → α) (f : α → ℝ) :
    (((List.finRange k).map g).map f).sum = ∑ o, f (g o) := by
  rw [List.map_map, Fin.sum_univ_def] <;> rfl

lemma sum_map_flatMap {α β : Type} (E : List α) (g : α → List β) (f : β → ℝ) :
    ((E.flatMap g).map f).sum = (E.map fun a ↦ ((g a).map f).sum).sum := by
  induction E with
  | nil => simp
  | cons a E ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

lemma sum_filter_split {α : Type} (p : α → Bool) (f : α → ℝ) (E : List α) :
    ((E.filter p).map f).sum + ((E.filter fun a ↦ !p a).map f).sum = (E.map f).sum := by
  induction E with
  | nil => simp
  | cons a E ih =>
    cases hpa : p a
    · simp [List.filter_cons, hpa] at ih ⊢
      linarith
    · simp [List.filter_cons, hpa] at ih ⊢
      linarith

lemma sum_filter_ite {α : Type} (p : α → Bool) (f : α → ℝ) (E : List α) :
    ((E.filter p).map f).sum = (E.map fun a ↦ if p a = true then f a else 0).sum := by
  induction E with
  | nil => simp
  | cons a E ih =>
    cases hpa : p a
    · simp [List.filter_cons, hpa, ih]
    · simp [List.filter_cons, hpa, ih]

lemma sum_map_neg' {α : Type} (E : List α) (f : α → ℝ) :
    (E.map fun a ↦ -f a).sum = -(E.map f).sum := by
  induction E with
  | nil => simp
  | cons a E ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

lemma sum_map_comb {α : Type} (E : List α) (f g : α → ℝ) :
    (E.map fun a ↦ 4 * f a - g a).sum = 4 * (E.map f).sum - (E.map g).sum := by
  induction E with
  | nil => simp
  | cons a E ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

lemma finset_sum_list_sum {α X : Type} [Fintype X] (E : List α) (g : X → α → ℝ) :
    ∑ x, (E.map (g x)).sum = (E.map fun a ↦ ∑ x, g x a).sum := by
  induction E with
  | nil => simp
  | cons a E ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-! ### Generic monotonicity of list sums along `ens` -/

section generic

variable {Var : Type} [DecidableEq Var] {ι : Type} {Q w : ℕ}

/-- If a weight `wt` does not decrease at each local step (on branches satisfying `I`, which is
preserved by `ens`), then the sum of `wt` over the list does not decrease along `ens`. -/
theorem ens_sum_mono
    (G : ι → ℕ → QRegister w Q → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (I : Branch Var ι Q → Prop) (wt : Branch Var ι Q → ℝ)
    (hinv : ∀ (P : LF Var Q w) (E : List (Branch Var ι Q)), (∀ β ∈ E, I β) →
      ∀ β ∈ ens G P E, I β)
    (hab : ∀ β, I β → wt β ≤ wt { β with live := false })
    (hst : ∀ (U : Unitary (2 ^ Q)) β, I β →
      wt β ≤ wt (if β.live then { β with vec := fun i ↦ U.1 *ᵥ β.vec i } else β))
    (hor : ∀ (r : QRegister w Q) β, I β →
      wt β ≤ wt (if β.live then
        { β with count := β.count + 1, vec := fun i ↦ G i β.count r *ᵥ β.vec i } else β))
    (hme : ∀ {k : ℕ} (v : Var) (r : QRegister k Q) (β : Branch Var ι Q), I β →
      wt β ≤ ((if β.live then
        (List.finRange (2 ^ k)).map fun o ↦
          { β with
            store := Function.update β.store v (o.val : ℤ)
            vec := fun i ↦ (r.computationalBasisMeasurement.1 o) *ᵥ β.vec i }
        else [β]).map wt).sum) :
    ∀ (P : LF Var Q w) (E : List (Branch Var ι Q)), (∀ β ∈ E, I β) →
      (E.map wt).sum ≤ ((ens G P E).map wt).sum := by
  intro P
  induction P with
  | skip =>
    intro E _
    exact le_of_eq (by simp only [ens])
  | abort =>
    intro E hE
    simp only [ens, List.map_map]
    exact List.sum_le_sum fun β hβ => hab β (hE β hβ)
  | step U =>
    intro E hE
    simp only [ens, List.map_map]
    exact List.sum_le_sum fun β hβ => hst U β (hE β hβ)
  | oracle r =>
    intro E hE
    simp only [ens, List.map_map]
    exact List.sum_le_sum fun β hβ => hor r β (hE β hβ)
  | @measure k v r =>
    intro E hE
    simp only [ens, sum_map_flatMap]
    exact List.sum_le_sum fun β hβ => hme v r β (hE β hβ)
  | @qIf b _ t f iht ihf =>
    intro E hE
    have h1 := iht (E.filter fun β ↦ decide (b β.store))
      (fun β hβ ↦ hE β (List.mem_of_mem_filter hβ))
    have h2 := ihf (E.filter fun β ↦ !decide (b β.store))
      (fun β hβ ↦ hE β (List.mem_of_mem_filter hβ))
    have hs := sum_filter_split (fun β : Branch Var ι Q ↦ decide (b β.store)) wt E
    simp only [ens, List.map_append, List.sum_append]
    linarith
  | seq p₁ p₂ ih₁ ih₂ =>
    intro E hE
    simp only [ens]
    exact (ih₁ E hE).trans (ih₂ _ (hinv p₁ E hE))

end generic

/-! ### Definitions for the hybrid runs -/

section hybrid

variable {Var : Type} [DecidableEq Var] {n Q : ℕ}

/-- Invariant: a branch that passed at most `l` oracle nodes has the reference vector in run
`(x, l)`. -/
def Inv (β : Branch Var (HIdx n) Q) : Prop :=
  ∀ (x : Fin (2 ^ n)) (l : ℕ), β.count ≤ l → β.vec (some (x, l)) = β.vec none

/-- Reference weight. -/
noncomputable def rw0 (β : Branch Var (HIdx n) Q) : ℝ := nsq (β.vec none)

/-- Squared distance between runs `(x, m)` and `(x, m + 1)`, summed over `x`. -/
noncomputable def gapB (m : ℕ) (β : Branch Var (HIdx n) Q) : ℝ :=
  ∑ x : Fin (2 ^ n), nsq (β.vec (some (x, m)) - β.vec (some (x, m + 1)))

/-- The potential of one branch at level `m`: counted once the branch passed `m + 1` oracle
nodes. -/
noncomputable def psiB (m : ℕ) (β : Branch Var (HIdx n) Q) : ℝ :=
  if m < β.count then 4 * rw0 β - gapB m β else 0

/-- The branch after an oracle node (live case). -/
noncomputable def orcB (r : QRegister ((n + 1) * 1) Q) (β : Branch Var (HIdx n) Q) :
    Branch Var (HIdx n) Q :=
  { β with count := β.count + 1, vec := fun i ↦ hybridG i β.count r *ᵥ β.vec i }

/-- The branch of outcome `o` after a measurement (live case). -/
noncomputable def measB {k : ℕ} (v : Var) (r : QRegister k Q) (β : Branch Var (HIdx n) Q)
    (o : Fin (2 ^ k)) : Branch Var (HIdx n) Q :=
  { β with
    store := Function.update β.store v (o.val : ℤ)
    vec := fun i ↦ (r.computationalBasisMeasurement.1 o) *ᵥ β.vec i }

lemma rw0_nonneg (β : Branch Var (HIdx n) Q) : 0 ≤ rw0 β := nsq_nonneg _

lemma hybridG_none (k : ℕ) (r : QRegister ((n + 1) * 1) Q) :
    (hybridG (n := n) (Q := Q) none k r : Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ) = 1 := rfl

lemma hybridG_some_le (x : Fin (2 ^ n)) (l k : ℕ) (r : QRegister ((n + 1) * 1) Q) (h : l ≤ k) :
    hybridG (some (x, l)) k r = (r.embedUnitary (groverParallelMarkingOracle 1 {x})).1 := by
  simp [hybridG, h]

lemma hybridG_some_gt (x : Fin (2 ^ n)) (l k : ℕ) (r : QRegister ((n + 1) * 1) Q) (h : k < l) :
    hybridG (some (x, l)) k r = 1 := by
  simp [hybridG, Nat.not_le.2 h]

/-! ### The invariant -/

lemma inv_abort {β : Branch Var (HIdx n) Q} (h : Inv β) : Inv { β with live := false } :=
  fun x l hl => h x l hl

lemma inv_step (U : Unitary (2 ^ Q)) {β : Branch Var (HIdx n) Q} (h : Inv β) :
    Inv (if β.live then { β with vec := fun i ↦ U.1 *ᵥ β.vec i } else β) := by
  by_cases hl : β.live = true
  · rw [if_pos hl]
    intro x l hl'
    show U.1 *ᵥ β.vec (some (x, l)) = U.1 *ᵥ β.vec none
    rw [h x l hl']
  · rw [if_neg hl]
    exact h

lemma inv_orcB (r : QRegister ((n + 1) * 1) Q) {β : Branch Var (HIdx n) Q} (h : Inv β) :
    Inv (orcB r β) := by
  intro x l hl
  have hl' : β.count + 1 ≤ l := hl
  show hybridG (some (x, l)) β.count r *ᵥ β.vec (some (x, l)) =
    hybridG none β.count r *ᵥ β.vec none
  rw [hybridG_some_gt x l _ r hl', hybridG_none, h x l (Nat.le_of_succ_le hl')]

lemma inv_orc (r : QRegister ((n + 1) * 1) Q) {β : Branch Var (HIdx n) Q} (h : Inv β) :
    Inv (if β.live then
      { β with count := β.count + 1, vec := fun i ↦ hybridG i β.count r *ᵥ β.vec i } else β) := by
  by_cases hl : β.live = true
  · rw [if_pos hl]
    exact inv_orcB r h
  · rw [if_neg hl]
    exact h

lemma inv_measB {k : ℕ} (v : Var) (r : QRegister k Q) (o : Fin (2 ^ k))
    {β : Branch Var (HIdx n) Q} (h : Inv β) : Inv (measB v r β o) := by
  intro x l hl
  show r.computationalBasisMeasurement.1 o *ᵥ β.vec (some (x, l)) =
    r.computationalBasisMeasurement.1 o *ᵥ β.vec none
  rw [h x l hl]

theorem inv_ens : ∀ (P : LF Var Q ((n + 1) * 1)) (E : List (Branch Var (HIdx n) Q)),
    (∀ β ∈ E, Inv β) → ∀ β ∈ ens hybridG P E, Inv β := by
  intro P
  induction P with
  | skip =>
    intro E hE β hβ
    exact hE β hβ
  | abort =>
    intro E hE β hβ
    simp only [ens, List.mem_map] at hβ
    obtain ⟨γ, hγ, rfl⟩ := hβ
    exact inv_abort (hE γ hγ)
  | step U =>
    intro E hE β hβ
    simp only [ens, List.mem_map] at hβ
    obtain ⟨γ, hγ, rfl⟩ := hβ
    exact inv_step U (hE γ hγ)
  | oracle r =>
    intro E hE β hβ
    simp only [ens, List.mem_map] at hβ
    obtain ⟨γ, hγ, rfl⟩ := hβ
    exact inv_orc r (hE γ hγ)
  | @measure k v r =>
    intro E hE β hβ
    simp only [ens, List.mem_flatMap] at hβ
    obtain ⟨γ, hγ, hβ⟩ := hβ
    by_cases hl : γ.live = true
    · rw [if_pos hl, List.mem_map] at hβ
      obtain ⟨o, _, rfl⟩ := hβ
      exact inv_measB v r o (hE γ hγ)
    · rw [if_neg hl, List.mem_singleton] at hβ
      rw [hβ]
      exact hE γ hγ
  | @qIf b _ t f iht ihf =>
    intro E hE β hβ
    simp only [ens, List.mem_append] at hβ
    rcases hβ with hβ | hβ
    · exact iht _ (fun γ hγ => hE γ (List.mem_of_mem_filter hγ)) β hβ
    · exact ihf _ (fun γ hγ => hE γ (List.mem_of_mem_filter hγ)) β hβ
  | seq p₁ p₂ ih₁ ih₂ =>
    intro E hE β hβ
    simp only [ens] at hβ
    exact ih₂ _ (ih₁ E hE) β hβ

lemma inv_init_list (σ₀ : Store Var) :
    ∀ β ∈ ([initBranch σ₀] : List (Branch Var (HIdx n) Q)), Inv β := by
  intro β hβ
  rw [List.mem_singleton] at hβ
  subst hβ
  exact fun _ _ _ => rfl

/-! ### Reference weight -/

lemma rw0_map (U : Unitary (2 ^ Q)) (β : Branch Var (HIdx n) Q) :
    rw0 { β with vec := fun i ↦ U.1 *ᵥ β.vec i } = rw0 β := by
  show nsq (U.1 *ᵥ β.vec none) = nsq (β.vec none)
  exact nsq_unit U _

lemma rw0_orcB (r : QRegister ((n + 1) * 1) Q) (β : Branch Var (HIdx n) Q) :
    rw0 (orcB r β) = rw0 β := by
  show nsq (hybridG none β.count r *ᵥ β.vec none) = nsq (β.vec none)
  rw [hybridG_none, Matrix.one_mulVec]

lemma sum_rw0_measB {k : ℕ} (v : Var) (r : QRegister k Q) (β : Branch Var (HIdx n) Q) :
    ∑ o : Fin (2 ^ k), rw0 (measB v r β o) = rw0 β :=
  sum_nsq_measure r.computationalBasisMeasurement (β.vec none)

lemma rw0_init (σ₀ : Store Var) : rw0 (initBranch σ₀ : Branch Var (HIdx n) Q) = 1 :=
  nsq_init Q

theorem rw0_ens (P : LF Var Q ((n + 1) * 1)) (E : List (Branch Var (HIdx n) Q))
    (hE : ∀ β ∈ E, Inv β) : ((ens hybridG P E).map rw0).sum ≤ (E.map rw0).sum := by
  have h := ens_sum_mono hybridG Inv (fun β ↦ -rw0 β) inv_ens
    (fun β _ => le_of_eq rfl)
    (fun U β _ => by
      by_cases h : β.live = true
      · rw [if_pos h]
        exact le_of_eq (by rw [rw0_map])
      · rw [if_neg h])
    (fun r β _ => by
      by_cases h : β.live = true
      · rw [if_pos h]
        exact le_of_eq (by show -rw0 β = -rw0 (orcB r β); rw [rw0_orcB])
      · rw [if_neg h])
    (fun {k} v r β _ => by
      by_cases h : β.live = true
      · rw [if_pos h, sum_finRange_map, Finset.sum_neg_distrib]
        exact neg_le_neg (le_of_eq (sum_rw0_measB v r β))
      · rw [if_neg h]
        simp)
    P E hE
  rw [sum_map_neg', sum_map_neg'] at h
  linarith

/-! ### The gap and the potential -/

lemma gap_map (U : Unitary (2 ^ Q)) (m : ℕ) (β : Branch Var (HIdx n) Q) :
    gapB m { β with vec := fun i ↦ U.1 *ᵥ β.vec i } = gapB m β := by
  unfold gapB
  refine Finset.sum_congr rfl fun x _ => ?_
  show nsq (U.1 *ᵥ β.vec (some (x, m)) - U.1 *ᵥ β.vec (some (x, m + 1))) =
    nsq (β.vec (some (x, m)) - β.vec (some (x, m + 1)))
  exact nsq_mulVec_sub U _ _

lemma sum_gap_measB {k : ℕ} (m : ℕ) (v : Var) (r : QRegister k Q) (β : Branch Var (HIdx n) Q) :
    ∑ o : Fin (2 ^ k), gapB m (measB v r β o) = gapB m β := by
  unfold gapB
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have key := sum_nsq_measure r.computationalBasisMeasurement
    (β.vec (some (x, m)) - β.vec (some (x, m + 1)))
  simp only [Matrix.mulVec_sub] at key
  exact key

lemma sum_psi_measB {k : ℕ} (m : ℕ) (v : Var) (r : QRegister k Q) (β : Branch Var (HIdx n) Q) :
    ∑ o : Fin (2 ^ k), psiB m (measB v r β o) = psiB m β := by
  by_cases hm : m < β.count
  · have h1 : ∀ o : Fin (2 ^ k), psiB m (measB v r β o) =
        4 * rw0 (measB v r β o) - gapB m (measB v r β o) := fun o => by
      unfold psiB
      exact if_pos hm
    rw [Finset.sum_congr rfl fun o _ => h1 o, Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_rw0_measB, sum_gap_measB]
    unfold psiB
    exact (if_pos hm).symm
  · have h1 : ∀ o : Fin (2 ^ k), psiB m (measB v r β o) = 0 := fun o => by
      unfold psiB
      exact if_neg hm
    rw [Finset.sum_congr rfl fun o _ => h1 o, Finset.sum_const_zero]
    unfold psiB
    exact (if_neg hm).symm

lemma psi_step (m : ℕ) (U : Unitary (2 ^ Q)) (β : Branch Var (HIdx n) Q) :
    psiB m β ≤ psiB m (if β.live then { β with vec := fun i ↦ U.1 *ᵥ β.vec i } else β) := by
  by_cases h : β.live = true
  · rw [if_pos h]
    refine le_of_eq ?_
    have h1 : rw0 ({ β with vec := fun i ↦ U.1 *ᵥ β.vec i } : Branch Var (HIdx n) Q) = rw0 β :=
      rw0_map U β
    have h2 : gapB m ({ β with vec := fun i ↦ U.1 *ᵥ β.vec i } : Branch Var (HIdx n) Q) =
        gapB m β := gap_map U m β
    simp only [psiB, h1, h2]
  · exact le_of_eq (by rw [if_neg h])

lemma psi_orcB (r : QRegister ((n + 1) * 1) Q) (m : ℕ) {β : Branch Var (HIdx n) Q} (hβ : Inv β) :
    psiB m β ≤ psiB m (orcB r β) := by
  have hr : rw0 (orcB r β) = rw0 β := rw0_orcB r β
  rcases lt_trichotomy m β.count with hlt | heq | hgt
  · -- the level was already counted: both runs apply the same unitary
    have hg : gapB m (orcB r β) = gapB m β := by
      unfold gapB
      refine Finset.sum_congr rfl fun x _ => ?_
      show nsq (hybridG (some (x, m)) β.count r *ᵥ β.vec (some (x, m)) -
          hybridG (some (x, m + 1)) β.count r *ᵥ β.vec (some (x, m + 1))) =
        nsq (β.vec (some (x, m)) - β.vec (some (x, m + 1)))
      rw [hybridG_some_le x m _ r hlt.le, hybridG_some_le x (m + 1) _ r (Nat.succ_le_of_lt hlt)]
      exact nsq_mulVec_sub _ _ _
    have h1 : psiB m β = 4 * rw0 β - gapB m β := by
      unfold psiB
      exact if_pos hlt
    have h2 : psiB m (orcB r β) = 4 * rw0 (orcB r β) - gapB m (orcB r β) := by
      unfold psiB
      exact if_pos (Nat.lt_succ_of_lt hlt)
    rw [h1, h2, hr, hg]
  · -- the level is counted for the first time: use the oracle locality bound
    have h0 : psiB m β = 0 := by
      unfold psiB
      exact if_neg (by omega)
    have h2 : psiB m (orcB r β) = 4 * rw0 (orcB r β) - gapB m (orcB r β) := by
      unfold psiB
      exact if_pos (by show m < β.count + 1; omega)
    have hg : gapB m (orcB r β) =
        ∑ x : Fin (2 ^ n), nsq ((r.embedUnitary (groverParallelMarkingOracle 1 {x})).1 *ᵥ
          β.vec none - β.vec none) := by
      unfold gapB
      refine Finset.sum_congr rfl fun x _ => ?_
      show nsq (hybridG (some (x, m)) β.count r *ᵥ β.vec (some (x, m)) -
          hybridG (some (x, m + 1)) β.count r *ᵥ β.vec (some (x, m + 1))) = _
      rw [hybridG_some_le x m _ r heq.le, hybridG_some_gt x (m + 1) _ r (by omega),
        Matrix.one_mulVec, hβ x m heq.ge, hβ x (m + 1) (by omega)]
    have key : ∑ x : Fin (2 ^ n), nsq ((r.embedUnitary (groverParallelMarkingOracle 1 {x})).1 *ᵥ
        β.vec none - β.vec none) ≤ 4 * nsq (β.vec none) := oracle_sq_sum_le r (β.vec none)
    have hr0 : rw0 β = nsq (β.vec none) := rfl
    rw [h0, h2, hr, hg, hr0]
    linarith
  · have h0 : psiB m β = 0 := by
      unfold psiB
      exact if_neg (by omega)
    have h2 : psiB m (orcB r β) = 0 := by
      unfold psiB
      exact if_neg (by show ¬ m < β.count + 1; omega)
    rw [h0, h2]

lemma psi_orc (r : QRegister ((n + 1) * 1) Q) (m : ℕ) {β : Branch Var (HIdx n) Q} (hβ : Inv β) :
    psiB m β ≤ psiB m (if β.live then
      { β with count := β.count + 1, vec := fun i ↦ hybridG i β.count r *ᵥ β.vec i } else β) := by
  by_cases h : β.live = true
  · rw [if_pos h]
    exact psi_orcB r m hβ
  · exact le_of_eq (by rw [if_neg h])

theorem psi_mono (m : ℕ) (P : LF Var Q ((n + 1) * 1)) (E : List (Branch Var (HIdx n) Q))
    (hE : ∀ β ∈ E, Inv β) :
    (E.map (psiB m)).sum ≤ ((ens hybridG P E).map (psiB m)).sum :=
  ens_sum_mono hybridG Inv (psiB m) inv_ens
    (fun β _ => le_of_eq rfl)
    (fun U β _ => psi_step m U β)
    (fun r β hβ => psi_orc r m hβ)
    (fun {k} v r β _ => by
      by_cases h : β.live = true
      · rw [if_pos h, sum_finRange_map]
        exact (sum_psi_measB m v r β).ge
      · rw [if_neg h]
        simp)
    P E hE

/-- On the final list the gaps sum to at most `4`. -/
theorem gap_sum_le (P : LF Var Q ((n + 1) * 1)) (σ₀ : Store Var) (m : ℕ) :
    (((ens hybridG P [initBranch σ₀]).map (gapB m))).sum ≤ 4 := by
  have hinv : ∀ β ∈ ens hybridG P [initBranch σ₀], Inv β :=
    inv_ens P _ (inv_init_list σ₀)
  have hr : ((ens hybridG P [initBranch σ₀]).map rw0).sum ≤ 1 :=
    (rw0_ens P _ (inv_init_list σ₀)).trans (by simp [rw0_init])
  have hpsi : 0 ≤ ((ens hybridG P [initBranch σ₀]).map (psiB m)).sum := by
    refine le_trans ?_ (psi_mono m P _ (inv_init_list σ₀))
    have : psiB m (initBranch σ₀ : Branch Var (HIdx n) Q) = 0 := by
      unfold psiB
      exact if_neg (Nat.not_lt_zero m)
    simp [this]
  have hpt : ∀ β ∈ ens hybridG P [initBranch σ₀], gapB m β ≤ 4 * rw0 β - psiB m β := by
    intro β hβ
    by_cases hm : m < β.count
    · have : psiB m β = 4 * rw0 β - gapB m β := by
        unfold psiB
        exact if_pos hm
      rw [this]
      linarith
    · have h0 : psiB m β = 0 := by
        unfold psiB
        exact if_neg hm
      have hg : gapB m β = 0 := by
        unfold gapB
        refine Finset.sum_eq_zero fun x _ => ?_
        rw [hinv β hβ x m (not_lt.1 hm), hinv β hβ x (m + 1) (by omega), sub_self]
        simp [nsq]
      rw [h0, hg]
      have := rw0_nonneg β
      linarith
  calc (((ens hybridG P [initBranch σ₀]).map (gapB m))).sum
      ≤ ((ens hybridG P [initBranch σ₀]).map fun β ↦ 4 * rw0 β - psiB m β).sum :=
        List.sum_le_sum hpt
    _ = 4 * ((ens hybridG P [initBranch σ₀]).map rw0).sum -
        ((ens hybridG P [initBranch σ₀]).map (psiB m)).sum := sum_map_comb _ _ _
    _ ≤ 4 := by linarith

end hybrid

/-! ### Flattening to one coordinate vector and Minkowski -/

lemma minkowski_sq {X : Type} [Fintype X] (a b : X → ℝ) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (ha : ∑ x, a x ^ 2 ≤ α ^ 2) (hb : ∑ x, b x ^ 2 ≤ β ^ 2) :
    ∑ x, (a x + b x) ^ 2 ≤ (α + β) ^ 2 := by
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have h1 : (∑ x, a x * b x) ^ 2 ≤ (α * β) ^ 2 := by
    refine cs.trans ?_
    calc (∑ x, a x ^ 2) * (∑ x, b x ^ 2) ≤ α ^ 2 * β ^ 2 :=
          mul_le_mul ha hb (Finset.sum_nonneg fun x _ => sq_nonneg _) (sq_nonneg α)
      _ = (α * β) ^ 2 := by ring
  have h2 : ∑ x, a x * b x ≤ α * β := (abs_le_of_sq_le_sq' h1 (mul_nonneg hα hβ)).2
  have h3 : ∑ x, (a x + b x) ^ 2 = ∑ x, a x ^ 2 + 2 * ∑ x, a x * b x + ∑ x, b x ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [h3]
  nlinarith

/-- Squared ℓ² norm of a complex coordinate vector on a finite index type. -/
noncomputable def nrm2 {X : Type} [Fintype X] (w : X → ℂ) : ℝ := ∑ i, Complex.normSq (w i)

lemma nrm2_add_le {X : Type} [Fintype X] (a b : X → ℂ) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (ha : nrm2 a ≤ α ^ 2) (hb : nrm2 b ≤ β ^ 2) : nrm2 (a + b) ≤ (α + β) ^ 2 := by
  have h := minkowski_sq (fun i ↦ ‖a i‖) (fun i ↦ ‖b i‖) α β hα hβ
    (by simpa [nrm2, Complex.sq_norm] using ha) (by simpa [nrm2, Complex.sq_norm] using hb)
  calc nrm2 (a + b) = ∑ i, ‖(a + b) i‖ ^ 2 := by simp [nrm2, Complex.sq_norm]
    _ ≤ ∑ i, (‖a i‖ + ‖b i‖) ^ 2 :=
      Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
    _ ≤ (α + β) ^ 2 := h

lemma nrm2_mono {X : Type} [Fintype X] (a b : X → ℂ)
    (h : ∀ p, Complex.normSq (a p) ≤ Complex.normSq (b p)) : nrm2 a ≤ nrm2 b :=
  Finset.sum_le_sum fun p _ => h p

/-- Chain of `T` steps of squared size `≤ 4`: the endpoints are `2 T` apart. -/
lemma chain_bound {X : Type} [Fintype X] (A : ℕ → X → ℂ) (h : ∀ m, nrm2 (A m - A (m + 1)) ≤ 4)
    (T : ℕ) : nrm2 (A 0 - A T) ≤ (2 * (T : ℝ)) ^ 2 := by
  induction T with
  | zero => simp [nrm2]
  | succ T ih =>
    have e : A 0 - A (T + 1) = (A 0 - A T) + (A T - A (T + 1)) := by abel
    rw [e]
    have := nrm2_add_le (A 0 - A T) (A T - A (T + 1)) (2 * (T : ℝ)) 2 (by positivity)
      (by norm_num) ih (le_trans (h T) (by norm_num))
    calc nrm2 ((A 0 - A T) + (A T - A (T + 1))) ≤ (2 * (T : ℝ) + 2) ^ 2 := this
      _ = (2 * ((T + 1 : ℕ) : ℝ)) ^ 2 := by push_cast; ring

/-- Flatten a family of vectors indexed by the elements of a list and a run index. -/
def flat {α : Type} {N M : ℕ} (L : List α) (a : α → Fin N → Fin M → ℂ) :
    Fin L.length × Fin N × Fin M → ℂ :=
  fun p ↦ a (L[p.1.1]'p.1.2) p.2.1 p.2.2

lemma nrm2_flat {α : Type} {N M : ℕ} (L : List α) (a : α → Fin N → Fin M → ℂ) :
    nrm2 (flat L a) = (L.map fun β ↦ ∑ x, ∑ j, Complex.normSq (a β x j)).sum := by
  rw [← Fin.sum_univ_fun_getElem L (fun β ↦ ∑ x, ∑ j, Complex.normSq (a β x j))]
  simp only [nrm2, flat, Fintype.sum_prod_type]

/-! ### The success bound -/

section success

variable {Var : Type} [DecidableEq Var] {n Q : ℕ}

/-- The branches that count for the marked item `x`. -/
def goodB (res : Var) (T : ℕ) (x : Fin (2 ^ n)) (β : Branch Var (HIdx n) Q) : Bool :=
  β.live && decide (β.count ≤ T) && decide (β.store res = (x.val : ℤ))

/-- The real run (x, 0) restricted to the good branches. -/
noncomputable def wv (res : Var) (T : ℕ) (β : Branch Var (HIdx n) Q) (x : Fin (2 ^ n))
    (j : Fin (2 ^ Q)) : ℂ :=
  if goodB res T x β = true then β.vec (some (x, 0)) j else 0

/-- The reference run restricted to the good branches. -/
noncomputable def wr (res : Var) (T : ℕ) (β : Branch Var (HIdx n) Q) (x : Fin (2 ^ n))
    (j : Fin (2 ^ Q)) : ℂ :=
  if goodB res T x β = true then β.vec none j else 0

lemma goodB_unique (res : Var) (T : ℕ) (β : Branch Var (HIdx n) Q) (x y : Fin (2 ^ n))
    (hx : goodB res T x β = true) (hy : goodB res T y β = true) : x = y := by
  simp only [goodB, Bool.and_eq_true, decide_eq_true_eq] at hx hy
  have h : (x.val : ℤ) = (y.val : ℤ) := hx.2.symm.trans hy.2
  exact Fin.ext (by exact_mod_cast h)

lemma sum_ite_le_of_unique {N : ℕ} (g : Fin N → Prop) [DecidablePred g]
    (hg : ∀ x y, g x → g y → x = y) (c : ℝ) (hc : 0 ≤ c) :
    ∑ x, (if g x then c else 0) ≤ c := by
  by_cases h : ∃ x, g x
  · obtain ⟨x0, hx0⟩ := h
    rw [Finset.sum_eq_single x0]
    · simp [hx0]
    · intro y _ hy
      rw [if_neg]
      intro hgy
      exact hy (hg y x0 hgy hx0)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · push_neg at h
    rw [Finset.sum_eq_zero]
    · exact hc
    · intro x _
      rw [if_neg (h x)]

lemma wr_sum_le (res : Var) (T : ℕ) (β : Branch Var (HIdx n) Q) :
    ∑ x : Fin (2 ^ n), ∑ j, Complex.normSq (wr res T β x j) ≤ rw0 β := by
  have h1 : ∀ x : Fin (2 ^ n), ∑ j, Complex.normSq (wr res T β x j) =
      if goodB res T x β = true then rw0 β else 0 := by
    intro x
    by_cases h : goodB res T x β = true
    · simp [wr, h, rw0, nsq]
    · simp [wr, h]
  rw [Finset.sum_congr rfl fun x _ => h1 x]
  exact sum_ite_le_of_unique (fun x => goodB res T x β = true) (goodB_unique res T β) (rw0 β)
    (rw0_nonneg β)

lemma e_pt (res : Var) (T : ℕ) (β : Branch Var (HIdx n) Q) (hβ : Inv β) (x : Fin (2 ^ n))
    (j : Fin (2 ^ Q)) :
    Complex.normSq (wv res T β x j - wr res T β x j) ≤
      Complex.normSq (β.vec (some (x, 0)) j - β.vec (some (x, T)) j) := by
  by_cases h : goodB res T x β = true
  · have hc : β.count ≤ T := by
      simp only [goodB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.2
    have e : β.vec (some (x, T)) = β.vec none := hβ x T hc
    simp only [wv, wr, h, if_true, e]
    exact le_refl _
  · simp [wv, wr, h]
    exact Complex.normSq_nonneg _

lemma lhs_eq (res : Var) (T : ℕ) (F : List (Branch Var (HIdx n) Q)) :
    ∑ x : Fin (2 ^ n), ((F.filter fun β ↦ β.live && decide (β.count ≤ T) &&
        decide (β.store res = (x.val : ℤ))).map fun β ↦ nsq (β.vec (some (x, 0)))).sum =
      nrm2 (flat F (wv res T)) := by
  have e1 : ∀ x : Fin (2 ^ n), ((F.filter fun β ↦ β.live && decide (β.count ≤ T) &&
        decide (β.store res = (x.val : ℤ))).map fun β ↦ nsq (β.vec (some (x, 0)))).sum =
      (F.map fun β ↦ if goodB res T x β = true then nsq (β.vec (some (x, 0))) else 0).sum :=
    fun x => sum_filter_ite (goodB res T x) _ F
  rw [Finset.sum_congr rfl fun x _ => e1 x, finset_sum_list_sum, nrm2_flat]
  refine congrArg List.sum (List.map_congr_left fun β _ => ?_)
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : goodB res T x β = true
  · simp [wv, h, nsq]
  · simp [wv, h]

end success

/-- **Main theorem.** Summed over the marked item `x`, the weight of the real run `(x, 0)` on live
branches that passed at most `T` oracle nodes and whose store holds `x` is at most
`(2 T + 1) ^ 2`. -/
theorem hybrid_success_le {Var : Type} [DecidableEq Var] (res : Var) (n Q T : ℕ)
    (P : LF Var Q ((n + 1) * 1)) (σ₀ : Store Var) :
    ∑ x : Fin (2 ^ n), (((ens hybridG P [initBranch σ₀]).filter fun β ↦
        β.live && decide (β.count ≤ T) && decide (β.store res = (x.val : ℤ))).map
        fun β ↦ nsq (β.vec (some (x, 0)))).sum ≤ (2 * (T : ℝ) + 1) ^ 2 := by
  rw [lhs_eq]
  set F := ens hybridG P [initBranch σ₀] with hF
  have hinv : ∀ β ∈ F, Inv β := inv_ens P _ (inv_init_list σ₀)
  have hr : (F.map rw0).sum ≤ 1 := (rw0_ens P _ (inv_init_list σ₀)).trans (by simp [rw0_init])
  -- the chain of runs `(x, m)`
  have hA : ∀ m : ℕ, nrm2 (flat F (fun β x j ↦ β.vec (some (x, m)) j) -
      flat F (fun β x j ↦ β.vec (some (x, m + 1)) j)) ≤ 4 := by
    intro m
    have e : flat F (fun β x j ↦ β.vec (some (x, m)) j) -
        flat F (fun β x j ↦ β.vec (some (x, m + 1)) j) =
        flat F (fun β x j ↦ β.vec (some (x, m)) j - β.vec (some (x, m + 1)) j) := rfl
    rw [e, nrm2_flat]
    exact gap_sum_le P σ₀ m
  have hchain := chain_bound (fun m ↦ flat F (fun β x j ↦ β.vec (some (x, m)) j)) hA T
  -- the difference between the real run and the reference run on the good branches
  have h_e : nrm2 (flat F (wv res T) - flat F (wr res T)) ≤ (2 * (T : ℝ)) ^ 2 := by
    refine le_trans (nrm2_mono _ _ ?_) hchain
    rintro ⟨i, x, j⟩
    exact e_pt res T (F[i.1]'i.2) (hinv _ (List.getElem_mem _)) x j
  have h_wr : nrm2 (flat F (wr res T)) ≤ 1 ^ 2 := by
    rw [nrm2_flat]
    calc (F.map fun β ↦ ∑ x, ∑ j, Complex.normSq (wr res T β x j)).sum
        ≤ (F.map rw0).sum := List.sum_le_sum fun β _ => wr_sum_le res T β
      _ ≤ 1 := hr
      _ = 1 ^ 2 := by norm_num
  have hdecomp : flat F (wr res T) + (flat F (wv res T) - flat F (wr res T)) =
      flat F (wv res T) := by abel
  calc nrm2 (flat F (wv res T))
      = nrm2 (flat F (wr res T) + (flat F (wv res T) - flat F (wr res T))) :=
        congrArg nrm2 hdecomp.symm
    _ ≤ (1 + 2 * (T : ℝ)) ^ 2 :=
        nrm2_add_le _ _ 1 (2 * (T : ℝ)) (by norm_num) (by positivity) h_wr h_e
    _ = (2 * (T : ℝ) + 1) ^ 2 := by ring

end GroverLowerBound

#print axioms GroverLowerBound.hybrid_success_le
