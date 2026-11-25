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
import LowerBounds.Grover.FindAllMatrixPotential
import LowerBounds.Grover.ParallelLink
import LowerBounds.Grover.ParallelOracle
import Mathlib

/-!
# The oracle hypothesis for the matrix potential

`HY Y D` says that the quadratic form `∑ (Y S S' - D S Y S S' D S') Re⟨u S, u S'⟩` is at most
`∑ ‖u S‖²` for all vectors `u`. `signX x` is the sign vector of the address `x` on `k`-sets.
`hH_of_split` and `hH_of_refl` reduce the drop of `gramY` under an oracle call to `HY` for the sign
vectors, through a decomposition of the call into orthogonal projectors, and `hH_single` applies
this to Google's marking oracle with one slot.
-/

open QuantumComputation.Specs Operator GroverLowerBound
open scoped Matrix

namespace GroverParallel

/-! ### The hypothesis on `Y` -/

/-- The form `∑ (Y S S' - D S Y S S' D S') Re⟨u S, u S'⟩` is dominated by `∑ ‖u S‖²`. -/
def HY {ι : Type} [Fintype ι] {d : ℕ} (Y : ι → ι → ℝ) (D : ι → ℝ) : Prop :=
  ∀ u : ι → Fin d → ℂ,
    ∑ S, ∑ S', (Y S S' - D S * Y S S' * D S') * (∑ j, star (u S j) * u S' j).re ≤ ∑ S, nsq (u S)

/-- the sign vector of address x on k-sets -/
def signX {n k : ℕ} (x : Fin (2 ^ n)) : KSet n k → ℝ := fun S => if x ∈ S.1 then -1 else 1

theorem HY_const_one {ι : Type} [Fintype ι] {d : ℕ} (Y : ι → ι → ℝ) :
    HY (d := d) Y (fun _ => 1) := by
  intro u
  have h0 : ∀ S S', (Y S S' - 1 * Y S S' * 1) = 0 := fun S S' => by ring
  simp only [h0, zero_mul, Finset.sum_const_zero]
  exact Finset.sum_nonneg fun S _ => nsq_nonneg _

/-! ### Real inner product -/

private def ipr {d : ℕ} (a b : Fin d → ℂ) : ℝ := (∑ j, star (a j) * b j).re

private lemma ipr_self {d : ℕ} (a : Fin d → ℂ) : ipr a a = nsq a := by
  unfold ipr
  simp [nsq, Complex.re_sum, Complex.normSq_apply]

private lemma ipr_mulVec2 {d : ℕ} (M N : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d → ℂ) :
    ipr (M *ᵥ a) (N *ᵥ b) = ipr a ((Mᴴ * N) *ᵥ b) := by
  show (star (M *ᵥ a) ⬝ᵥ (N *ᵥ b)).re = (star a ⬝ᵥ ((Mᴴ * N) *ᵥ b)).re
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

private lemma ipr_sum_smul {κ : Type} [Fintype κ] {d : ℕ} (a : Fin d → ℂ) (c : κ → ℝ)
    (x : κ → Fin d → ℂ) :
    ipr a (∑ p, ((c p : ℝ) : ℂ) • x p) = ∑ p, c p * ipr a (x p) := by
  unfold ipr
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_left_comm, Complex.re_ofReal_mul]

private lemma ipr_sum_mat {κ : Type} [Fintype κ] {d : ℕ} (P : κ → Matrix (Fin d) (Fin d) ℂ)
    (c : κ → ℝ) (a b : Fin d → ℂ) :
    ipr a ((∑ p, ((c p : ℝ) : ℂ) • P p) *ᵥ b) = ∑ p, c p * ipr a (P p *ᵥ b) := by
  rw [Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec]
  exact ipr_sum_smul a c (fun p => P p *ᵥ b)

private lemma star_ofReal' (c : ℝ) : star ((c : ℝ) : ℂ) = (c : ℂ) := Complex.conj_ofReal c

/-! ### The generic split -/

/-- If `G S = ∑ p, ε p S • P p` for a resolution of the identity `P` by pairwise orthogonal
self-adjoint idempotents, and `HY Y (ε p)` holds for every `p`, then the potential drop of `G` is
at most the total squared norm. -/
theorem hH_of_split {ι κ : Type} [Fintype ι] [Fintype κ] {Q : ℕ}
    (Y : ι → ι → ℝ) (G : ι → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (P : κ → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ) (ε : κ → ι → ℝ)
    (hsa : ∀ p, (P p)ᴴ = P p) (hid : ∀ p, P p * P p = P p)
    (horth : ∀ p q, p ≠ q → P p * P q = 0) (hsum : ∑ p, P p = 1)
    (hG : ∀ S, G S = ∑ p, ((ε p S : ℝ) : ℂ) • P p)
    (hε : ∀ p, HY (d := 2 ^ Q) Y (ε p)) (v : ι → Fin (2 ^ Q) → ℂ) :
    gramY Y v - gramY Y (fun S => G S *ᵥ v S) ≤ ∑ S, nsq (v S) := by
  have hPP : ∀ p a b, ipr (P p *ᵥ a) (P p *ᵥ b) = ipr a (P p *ᵥ b) := by
    intro p a b
    rw [ipr_mulVec2, hsa, hid]
  have hcomplete : ∀ a b, ipr a b = ∑ p, ipr a (P p *ᵥ b) := by
    intro a b
    have hb : b = ∑ p, ((1 : ℝ) : ℂ) • (P p *ᵥ b) := by
      simp only [Complex.ofReal_one, one_smul]
      rw [← Matrix.sum_mulVec, hsum, Matrix.one_mulVec]
    conv_lhs => rw [hb]
    rw [ipr_sum_smul]
    simp
  have key : ∀ S S' a b, ipr a b - ipr (G S *ᵥ a) (G S' *ᵥ b) =
      ∑ p, (1 - ε p S * ε p S') * ipr (P p *ᵥ a) (P p *ᵥ b) := by
    intro S S' a b
    have hK : (G S)ᴴ * G S' = ∑ p, ((ε p S * ε p S' : ℝ) : ℂ) • P p := by
      rw [hG S, hG S', Matrix.conjTranspose_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum, Finset.sum_eq_single p]
      · rw [Matrix.conjTranspose_smul, hsa, Matrix.smul_mul, Matrix.mul_smul, hid, smul_smul,
          star_ofReal', Complex.ofReal_mul]
      · intro q _ hq
        rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hsa,
          horth p q (Ne.symm hq)]
        simp
      · intro h
        exact absurd (Finset.mem_univ p) h
    rw [ipr_mulVec2, hK, ipr_sum_mat, hcomplete a b, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hPP]
    ring
  have hsq : ∀ w, ∑ p, nsq (P p *ᵥ w) = nsq w := by
    intro w
    have h := hcomplete w w
    rw [ipr_self] at h
    rw [h]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← ipr_self, hPP]
  have hrow : ∀ S, ∑ S', Y S S' * (ipr (v S) (v S') - ipr (G S *ᵥ v S) (G S' *ᵥ v S')) =
      ∑ p, ∑ S', (Y S S' - ε p S * Y S S' * ε p S') * ipr (P p *ᵥ v S) (P p *ᵥ v S') := by
    intro S
    calc ∑ S', Y S S' * (ipr (v S) (v S') - ipr (G S *ᵥ v S) (G S' *ᵥ v S'))
        = ∑ S', ∑ p, Y S S' * ((1 - ε p S * ε p S') * ipr (P p *ᵥ v S) (P p *ᵥ v S')) :=
          Finset.sum_congr rfl fun S' _ => by rw [key, Finset.mul_sum]
      _ = ∑ p, ∑ S', Y S S' * ((1 - ε p S * ε p S') * ipr (P p *ᵥ v S) (P p *ᵥ v S')) :=
          Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun S' _ => by ring
  calc gramY Y v - gramY Y (fun S => G S *ᵥ v S)
      = ∑ S, ∑ S', Y S S' * (ipr (v S) (v S') - ipr (G S *ᵥ v S) (G S' *ᵥ v S')) := by
        show ∑ S, ∑ S', Y S S' * ipr (v S) (v S') -
          ∑ S, ∑ S', Y S S' * ipr (G S *ᵥ v S) (G S' *ᵥ v S') = _
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun S' _ => ?_
        ring
    _ = ∑ S, ∑ p, ∑ S', (Y S S' - ε p S * Y S S' * ε p S') *
          ipr (P p *ᵥ v S) (P p *ᵥ v S') := Finset.sum_congr rfl fun S _ => hrow S
    _ = ∑ p, ∑ S, ∑ S', (Y S S' - ε p S * Y S S' * ε p S') *
          ipr (P p *ᵥ v S) (P p *ᵥ v S') := Finset.sum_comm
    _ ≤ ∑ p, ∑ S, nsq (P p *ᵥ v S) :=
        Finset.sum_le_sum fun p _ => hε p (fun S => P p *ᵥ v S)
    _ = ∑ S, ∑ p, nsq (P p *ᵥ v S) := Finset.sum_comm
    _ = ∑ S, nsq (v S) := Finset.sum_congr rfl fun S _ => hsq (v S)

/-! ### Reflections: `G S = 1 + ∑ x, (ε x S - 1) • P x` -/

/-- The projector `(1/2) (E x - E x * F)` onto the `-1` eigenspace of `F` inside the range of `E x`. -/
noncomputable def reflProj {α : Type} {d : ℕ} (E : α → Matrix (Fin d) (Fin d) ℂ)
    (F : Matrix (Fin d) (Fin d) ℂ) (x : α) : Matrix (Fin d) (Fin d) ℂ :=
  (1 / 2 : ℂ) • (E x - E x * F)

private lemma star_half : star (1 / 2 : ℂ) = 1 / 2 := by
  have h : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [h]
  exact star_ofReal' _

private lemma reflProj_sa {α : Type} {d : ℕ} (E : α → Matrix (Fin d) (Fin d) ℂ)
    (F : Matrix (Fin d) (Fin d) ℂ) (hEsa : ∀ x, (E x)ᴴ = E x) (hFsa : Fᴴ = F)
    (hcomm : ∀ x, F * E x = E x * F) (x : α) : (reflProj E F x)ᴴ = reflProj E F x := by
  unfold reflProj
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hEsa, hFsa,
    hcomm x, star_half]

private lemma reflProj_id {α : Type} {d : ℕ} (E : α → Matrix (Fin d) (Fin d) ℂ)
    (F : Matrix (Fin d) (Fin d) ℂ) (hEid : ∀ x, E x * E x = E x) (hFinv : F * F = 1)
    (hcomm : ∀ x, F * E x = E x * F) (x : α) :
    reflProj E F x * reflProj E F x = reflProj E F x := by
  have e1 : E x * F * E x = E x * F := by
    rw [mul_assoc, hcomm x, ← mul_assoc, hEid]
  have e2 : E x * F * (E x * F) = E x := by
    rw [← mul_assoc, e1, mul_assoc, hFinv, mul_one]
  have e3 : E x * (E x * F) = E x * F := by
    rw [← mul_assoc, hEid]
  have hsq : (E x - E x * F) * (E x - E x * F) = (E x - E x * F) + (E x - E x * F) := by
    simp only [mul_sub, sub_mul, hEid, e1, e2, e3]
    abel
  unfold reflProj
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsq, ← two_smul ℂ, smul_smul]
  congr 1
  norm_num

private lemma reflProj_orth {α : Type} {d : ℕ} (E : α → Matrix (Fin d) (Fin d) ℂ)
    (F : Matrix (Fin d) (Fin d) ℂ) (hEorth : ∀ x y, x ≠ y → E x * E y = 0)
    (hFinv : F * F = 1) (hcomm : ∀ x, F * E x = E x * F) (x y : α) (hxy : x ≠ y) :
    reflProj E F x * reflProj E F y = 0 := by
  have e : E x * F * E y = E x * E y * F := by
    rw [mul_assoc, hcomm y, ← mul_assoc]
  have e' : E x * F * (E y * F) = E x * E y := by
    rw [← mul_assoc, e, mul_assoc, hFinv, mul_one]
  have e'' : E x * (E y * F) = E x * E y * F := (mul_assoc _ _ _).symm
  have h0 : (E x - E x * F) * (E y - E y * F) = 0 := by
    simp only [mul_sub, sub_mul, e, e', e'', hEorth x y hxy, zero_mul, sub_self]
  unfold reflProj
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h0, smul_zero]

/-- A family of orthogonal self-adjoint idempotents together with the complement of their sum. -/
private lemma comp_family {α : Type} [Fintype α] {d : ℕ} (Pa : α → Matrix (Fin d) (Fin d) ℂ)
    (hsa : ∀ x, (Pa x)ᴴ = Pa x) (hid : ∀ x, Pa x * Pa x = Pa x)
    (horth : ∀ x y, x ≠ y → Pa x * Pa y = 0) :
    (1 - ∑ x, Pa x)ᴴ = 1 - ∑ x, Pa x ∧
    (1 - ∑ x, Pa x) * (1 - ∑ x, Pa x) = 1 - ∑ x, Pa x ∧
    (∀ x, (1 - ∑ y, Pa y) * Pa x = 0) ∧ (∀ x, Pa x * (1 - ∑ y, Pa y) = 0) := by
  have hl : ∀ x, (∑ y, Pa y) * Pa x = Pa x := by
    intro x
    rw [Finset.sum_mul, Finset.sum_eq_single x]
    · exact hid x
    · intro y _ hy
      exact horth y x hy
    · intro h
      exact absurd (Finset.mem_univ x) h
  have hr : ∀ x, Pa x * (∑ y, Pa y) = Pa x := by
    intro x
    rw [Finset.mul_sum, Finset.sum_eq_single x]
    · exact hid x
    · intro y _ hy
      exact horth x y (Ne.symm hy)
    · intro h
      exact absurd (Finset.mem_univ x) h
  have h3 : ∀ x, (1 - ∑ y, Pa y) * Pa x = 0 := by
    intro x
    rw [sub_mul, one_mul, hl, sub_self]
  have h4 : ∀ x, Pa x * (1 - ∑ y, Pa y) = 0 := by
    intro x
    rw [mul_sub, mul_one, hr, sub_self]
  refine ⟨?_, ?_, h3, h4⟩
  · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_sum]
    simp only [hsa]
  · calc (1 - ∑ x, Pa x) * (1 - ∑ x, Pa x)
        = (1 - ∑ x, Pa x) - (1 - ∑ x, Pa x) * ∑ x, Pa x := by rw [mul_sub, mul_one]
      _ = 1 - ∑ x, Pa x := by
        rw [Finset.mul_sum, Finset.sum_eq_zero fun y _ => h3 y, sub_zero]

/-- The reflection split: `G S = 1 + ∑ x, (ε x S - 1) • reflProj E F x`. -/
theorem hH_of_refl {ι α : Type} [Fintype ι] [Fintype α] {Q : ℕ}
    (Y : ι → ι → ℝ) (G : ι → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (E : α → Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ) (F : Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)
    (ε : α → ι → ℝ)
    (hEsa : ∀ x, (E x)ᴴ = E x) (hEid : ∀ x, E x * E x = E x)
    (hEorth : ∀ x y, x ≠ y → E x * E y = 0) (hFsa : Fᴴ = F) (hFinv : F * F = 1)
    (hcomm : ∀ x, F * E x = E x * F)
    (hG : ∀ S, G S = 1 + ∑ x, (((ε x S : ℝ) : ℂ) - 1) • reflProj E F x)
    (hε : ∀ x, HY (d := 2 ^ Q) Y (ε x)) (v : ι → Fin (2 ^ Q) → ℂ) :
    gramY Y v - gramY Y (fun S => G S *ᵥ v S) ≤ ∑ S, nsq (v S) := by
  have hsaX := reflProj_sa E F hEsa hFsa hcomm
  have hidX := reflProj_id E F hEid hFinv hcomm
  have horthX := reflProj_orth E F hEorth hFinv hcomm
  obtain ⟨h0sa, h0id, h0x, hx0⟩ := comp_family (reflProj E F) hsaX hidX horthX
  refine hH_of_split (κ := Option α) Y G
    (fun o => Option.elim o (1 - ∑ x, reflProj E F x) (fun x => reflProj E F x))
    (fun o => Option.elim o (fun _ => 1) ε) ?_ ?_ ?_ ?_ ?_ ?_ v
  · rintro (_ | x)
    · exact h0sa
    · exact hsaX x
  · rintro (_ | x)
    · exact h0id
    · exact hidX x
  · rintro (_ | p) (_ | q) hpq
    · exact absurd rfl hpq
    · exact h0x q
    · exact hx0 p
    · exact horthX p q fun h => hpq (by rw [h])
  · rw [Fintype.sum_option]
    simp only [Option.elim_none, Option.elim_some]
    abel
  · intro S
    rw [Fintype.sum_option, hG S]
    simp only [Option.elim_none, Option.elim_some, Complex.ofReal_one, one_smul, sub_smul,
      Finset.sum_sub_distrib]
    abel
  · rintro (_ | x)
    · exact HY_const_one Y
    · exact hε x

/-! ### The oracle at `m = 1` -/

private lemma laddr_cflip {n : ℕ} (y : Fin (2 ^ (n + 1))) : laddr (cflip n y) = laddr y := by
  have hm : tableAddPerm (fun _ : Fin (2 ^ n) => (1 : Fin (2 ^ 1))) (cflip n y) = y := by
    unfold cflip
    exact Equiv.apply_symm_apply _ _
  have h := laddr_tableAddPerm (fun _ : Fin (2 ^ n) => (1 : Fin (2 ^ 1))) (cflip n y)
  rw [hm] at h
  exact h.symm

private lemma inv_apply_one {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ 1)) (l : Fin (2 ^ (n + 1)))
    (h : f (laddr l) = 1) : (tableAddPerm f)⁻¹ l = cflip n l := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  have hm : tableAddPerm (fun _ : Fin (2 ^ n) => (1 : Fin (2 ^ 1))) (cflip n l) = l := by
    unfold cflip
    exact Equiv.apply_symm_apply _ _
  have haddr : laddr (cflip n l) = laddr l := laddr_cflip l
  have key : tableAddPerm f (cflip n l) =
      tableAddPerm (fun _ : Fin (2 ^ n) => (1 : Fin (2 ^ 1))) (cflip n l) := by
    apply (splitBasisEquiv n 1).injective
    rw [split_tableAddPerm, split_tableAddPerm]
    have h1 : f (splitBasisEquiv n 1 (cflip n l)).1 = 1 := by
      have h2 : (splitBasisEquiv n 1 (cflip n l)).1 = laddr l := haddr
      rw [h2]
      exact h
    exact congrArg (fun y => ((splitBasisEquiv n 1 (cflip n l)).1,
      (splitBasisEquiv n 1 (cflip n l)).2 + y)) h1
  exact (key.trans hm).symm

private lemma inv_apply_zero {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ 1)) (l : Fin (2 ^ (n + 1)))
    (h : f (laddr l) = 0) : (tableAddPerm f)⁻¹ l = l := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  exact (tableAddPerm_eq_self f l h).symm

private lemma oracle_val' {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) (S : Finset (Fin (2 ^ n))) :
    (r.embedUnitary (groverParallelMarkingOracle 1 S)).1 =
      (GroverLowerBound.oreg r).embedMatrix
        (((tableAddPerm (fun x : Fin (2 ^ n) => if x ∈ S then (1 : Fin (2 ^ 1)) else 0))⁻¹).permMatrix ℂ) := by
  rw [GroverLowerBound.parallel_one, ← QRegister.embedUnitary_compose]
  rfl

private lemma oracle_apply {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) (S : Finset (Fin (2 ^ n)))
    (w : Fin (2 ^ Q) → ℂ) (l : Fin (2 ^ Q)) :
    ((r.embedUnitary (groverParallelMarkingOracle 1 S)).1 *ᵥ w) l =
      if GroverLowerBound.addr r l ∈ S then w (GroverLowerBound.flipEquiv (GroverLowerBound.oreg r) l) else w l := by
  rw [oracle_val', GroverLowerBound.perm_apply]
  by_cases h : GroverLowerBound.addr r l ∈ S
  · have h' : laddr ((GroverLowerBound.oreg r).extractIndex l) ∈ S := h
    have hf : (fun x : Fin (2 ^ n) => if x ∈ S then (1 : Fin (2 ^ 1)) else 0)
        (laddr ((GroverLowerBound.oreg r).extractIndex l)) = 1 := if_pos h'
    rw [if_pos h, inv_apply_one _ _ hf, GroverLowerBound.flipEquiv_apply]
  · have h' : laddr ((GroverLowerBound.oreg r).extractIndex l) ∉ S := h
    have hf : (fun x : Fin (2 ^ n) => if x ∈ S then (1 : Fin (2 ^ 1)) else 0)
        (laddr ((GroverLowerBound.oreg r).extractIndex l)) = 0 := if_neg h'
    rw [if_neg h, inv_apply_zero _ _ hf]
    exact congrArg w (QRegister.replaceIndex_extractIndex _ _)

private lemma addr_flip {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) (l : Fin (2 ^ Q)) :
    GroverLowerBound.addr r (GroverLowerBound.flipEquiv (GroverLowerBound.oreg r) l) = GroverLowerBound.addr r l := by
  rw [GroverLowerBound.addr_eq, GroverLowerBound.addr_eq, GroverLowerBound.flipEquiv_apply, QRegister.extractIndex_replaceIndex]
  exact laddr_cflip _

private lemma mulVec_single_apply' {d : Type*} [Fintype d] [DecidableEq d]
    (M : Matrix d d ℂ) (j l : d) : (M *ᵥ Pi.single j (1 : ℂ)) l = M l j := by
  rw [Matrix.mulVec_single_one]
  rfl

private lemma matrix_ext_mulVec {d : ℕ} (M N : Matrix (Fin d) (Fin d) ℂ)
    (h : ∀ w, M *ᵥ w = N *ᵥ w) : M = N := by
  ext l j
  have h1 := congrFun (h (Pi.single j 1)) l
  rw [mulVec_single_apply', mulVec_single_apply'] at h1
  exact h1

/-- The diagonal projector onto the basis states of address `x`. -/
private noncomputable def Em {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) (x : Fin (2 ^ n)) :
    Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ :=
  Matrix.diagonal fun l => if GroverLowerBound.addr r l = x then (1 : ℂ) else 0

/-- The oracle for the full address set: it flips the answer qubit at every address. -/
private noncomputable def Fm {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) :
    Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ :=
  (r.embedUnitary (groverParallelMarkingOracle 1 Finset.univ)).1

private lemma Em_apply {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) (x : Fin (2 ^ n))
    (w : Fin (2 ^ Q) → ℂ) (l : Fin (2 ^ Q)) :
    (Em r x *ᵥ w) l = if GroverLowerBound.addr r l = x then w l else 0 := by
  unfold Em
  rw [Matrix.mulVec_diagonal]
  split_ifs <;> simp

private lemma Fm_apply {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) (w : Fin (2 ^ Q) → ℂ)
    (l : Fin (2 ^ Q)) : (Fm r *ᵥ w) l = w (GroverLowerBound.flipEquiv (GroverLowerBound.oreg r) l) := by
  unfold Fm
  rw [oracle_apply, if_pos (Finset.mem_univ _)]

private lemma Em_sa {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) (x : Fin (2 ^ n)) :
    (Em r x)ᴴ = Em r x := by
  unfold Em
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext l
  by_cases h : GroverLowerBound.addr r l = x <;> simp [h]

private lemma Em_id {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) (x : Fin (2 ^ n)) :
    Em r x * Em r x = Em r x := by
  unfold Em
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext l
  split_ifs <;> simp

private lemma Em_orth {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) (x y : Fin (2 ^ n))
    (hxy : x ≠ y) : Em r x * Em r y = 0 := by
  unfold Em
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
  congr 1
  funext l
  by_cases h : GroverLowerBound.addr r l = x
  · have h2 : ¬ GroverLowerBound.addr r l = y := fun h2 => hxy (h.symm.trans h2)
    simp [h, h2, hxy]
  · simp [h]

private lemma Fm_sa {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) : (Fm r)ᴴ = Fm r :=
  parallelOracle_selfAdjoint r Finset.univ

private lemma Fm_inv {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) : Fm r * Fm r = 1 :=
  parallelOracle_mul_self r Finset.univ

private lemma Fm_comm {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) (x : Fin (2 ^ n)) :
    Fm r * Em r x = Em r x * Fm r := by
  apply matrix_ext_mulVec
  intro w
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  funext l
  simp only [Fm_apply, Em_apply, addr_flip]

private lemma proj_apply {n Q : ℕ} (r : QRegister ((n + 1) * 1) Q) (x : Fin (2 ^ n))
    (w : Fin (2 ^ Q) → ℂ) (l : Fin (2 ^ Q)) :
    (reflProj (Em r) (Fm r) x *ᵥ w) l =
      if GroverLowerBound.addr r l = x then (1 / 2 : ℂ) * (w l - w (GroverLowerBound.flipEquiv (GroverLowerBound.oreg r) l)) else 0 := by
  have h : reflProj (Em r) (Fm r) x *ᵥ w =
      (1 / 2 : ℂ) • (Em r x *ᵥ w - Em r x *ᵥ (Fm r *ᵥ w)) := by
    unfold reflProj
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.mulVec_mulVec]
  rw [h, Pi.smul_apply, Pi.sub_apply, Em_apply, Em_apply, Fm_apply, smul_eq_mul]
  by_cases hx : GroverLowerBound.addr r l = x
  · simp [hx]
  · simp [hx]

private lemma GK_eq_refl {n k Q : ℕ} (r : QRegister ((n + 1) * 1) Q) (S : KSet n k) (c : ℕ) :
    GK n 1 k Q S c r =
      1 + ∑ x, (((signX x S : ℝ) : ℂ) - 1) • reflProj (Em r) (Fm r) x := by
  apply matrix_ext_mulVec
  intro w
  funext l
  have hL : (GK n 1 k Q S c r *ᵥ w) l =
      if GroverLowerBound.addr r l ∈ S.1 then w (GroverLowerBound.flipEquiv (GroverLowerBound.oreg r) l) else w l :=
    oracle_apply r S.1 w l
  rw [hL]
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec,
    Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, proj_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases h : GroverLowerBound.addr r l ∈ S.1
  · simp only [signX, if_pos h]
    push_cast
    ring
  · simp only [signX, if_neg h]
    push_cast
    ring

/-- The hypothesis `hH` of `pwY_ens_mono` for the spec's oracle at `m = 1`, from `HY` for the
address sign vectors. -/
theorem hH_single {n k Q : ℕ} (Y : KSet n k → KSet n k → ℝ)
    (hY : ∀ x : Fin (2 ^ n), HY (d := 2 ^ Q) Y (signX x))
    (c : ℕ) (r : QRegister ((n + 1) * 1) Q) (v : KSet n k → Fin (2 ^ Q) → ℂ) :
    gramY Y v - gramY Y (fun S => GK n 1 k Q S c r *ᵥ v S) ≤ ∑ S, nsq (v S) :=
  hH_of_refl Y (fun S => GK n 1 k Q S c r) (Em r) (Fm r) (fun x S => signX x S)
    (Em_sa r) (Em_id r) (Em_orth r) (Fm_sa r) (Fm_inv r) (Fm_comm r)
    (fun S => GK_eq_refl r S c) hY v

end GroverParallel

#print axioms GroverParallel.HY_const_one
#print axioms GroverParallel.hH_of_split
#print axioms GroverParallel.hH_of_refl
#print axioms GroverParallel.hH_single
