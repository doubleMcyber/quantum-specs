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
# Less-Than Comparison (`comparator`) Specification: Baseline Solution

Baseline: subtract `y` from a `(k + 1)`-bit copy of `x` in place with the ripple-carry adder run
backwards (`ArcsinImpl.rippleSteps` of the `arcsin` solution in `QuantumComputationDiscoveries`),
copy the borrow bit onto the flag `t` by a `CNOT`, and add `y` back. It uses `k + 3` clean ancillas
(the two extension bits, one zero carry-in wire and `k` carry wires) and at most `8 * k` `T` gates.
The specification text below is unchanged; only the holes are filled and the theorems proved.

Parameterized specification for reversible comparison of two `k`-bit quantum registers,
`|y⟩|x⟩|t⟩|0⟩^⊗m ↦ |y⟩|x⟩|t ⊕ [x < y]⟩|0⟩^⊗m`, for every bit-width `k`. Both registers hold unsigned
integers in `[0, 2^k)`, least-significant bit first, and are preserved. The flag qubit `t` is
flipped exactly when `x < y` (strict), and the `m` clean ancilla qubits are returned to zero. The
other three order relations follow by exchanging the registers or applying an `X` gate to the flag,
at no `T` cost. Kets are written with the most significant register on the left, so the rightmost
register occupies the lowest wires.

There are two resource metrics over Clifford + `T` with measurements: the `T` count, and spacetime
(`T count * qubits`), where `qubits = 2 * k + 1 + comparatorAncillas k` is the total number of data
and clean ancilla qubits. Each metric has three cost theorems. One bounds the cost at every
bit-width `k` by a claimed function of `k`. The other two pin the bit-widths `k = 64` and `k = 2048`
and bound the cost by a claimed closed constant, so that two solutions can be compared by a number.
`TOFF` gates are excluded, so each Toffoli is costed by its Clifford + `T` construction, such as `4`
`T` gates with an ancilla and a measurement (C. Jones, Phys. Rev. A 87, 022328 (2013)).

References for the textbook constructions:
* S. A. Cuccaro, T. G. Draper, S. A. Kutin, D. P. Moulton, "A new quantum ripple-carry addition
  circuit", arXiv:quant-ph/0410184.
* C. Gidney, "Halving the cost of quantum addition", Quantum 2, 74 (2018), arXiv:1709.06648.
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator

/-!
## Reversible Comparison Unitary
-/

/-- The comparison flag `[x < y]` as a one-bit table on a `2k`-qubit basis index, which
`splitEqualBasisEquiv` splits into `y` (high half) and `x` (low half). -/
def lessThanFlag (k : ℕ) (u : Fin (2 ^ (2 * k))) : Fin (2 ^ 1) :=
  if (splitEqualBasisEquiv k u).2 < (splitEqualBasisEquiv k u).1 then 1 else 0

/-- Ideal `(2k + 1)`-qubit unitary `|y⟩|x⟩|t⟩ ↦ |y⟩|x⟩|t ⊕ [x < y]⟩`: the basis permutation
`tableAddPerm` of `lessThanFlag`, with the flag `t` as the lowest bit of the basis index. -/
noncomputable abbrev comparatorUnitary (k : ℕ) : Unitary (2 ^ (2 * k + 1)) :=
  permutationUnitary (tableAddPerm (lessThanFlag k))

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive Comparator.Var where | v deriving DecidableEq, Inhabited

open Comparator (Var)
open Comparator.Var (v)

/-!
## Baseline Construction
-/

namespace ComparatorImpl

open ArcsinImpl ArcsinImpl.Step Function

variable {n : ℕ}

/-- Disjointness of two registers is decidable (computably), so that the step list can be defined
for every pair of registers, with the empty list for overlapping ones. -/
instance decDisjoint {k m : ℕ} (r : QRegister k n) (s : QRegister m n) :
    Decidable (r.DisjointWires s) :=
  decidable_of_iff (∀ i j, r i ≠ s j) QRegister.disjoint_iff.symm

/-! ### Arithmetic -/

/-- Subtracting `y` modulo `2 * P` and adding it back returns `x`. -/
theorem sub_arith (P x y : ℕ) (hx : x < P) (hy : y < P) :
    (y + (x + 2 * P - y) % (2 * P)) % (2 * P) = x := by
  by_cases h : y ≤ x
  · have e : (x + 2 * P - y) % (2 * P) = x - y := by
      rw [show x + 2 * P - y = (x - y) + 2 * P by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [e, show y + (x - y) = x by omega, Nat.mod_eq_of_lt (by omega)]
  · have e : (x + 2 * P - y) % (2 * P) = x + 2 * P - y := Nat.mod_eq_of_lt (by omega)
    rw [e, show y + (x + 2 * P - y) = x + 2 * P by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]

/-- The bit `P` of `x - y` modulo `2 * P` is the borrow `[x < y]`. -/
theorem borrow_arith (P x y : ℕ) (hP : 0 < P) (hx : x < P) (hy : y < P) :
    (x + 2 * P - y) % (2 * P) / P % 2 = if x < y then 1 else 0 := by
  by_cases h : x < y
  · simp only [h, ↓reduceIte]
    have e : (x + 2 * P - y) % (2 * P) = x + 2 * P - y := Nat.mod_eq_of_lt (by omega)
    have e2 : (x + 2 * P - y) / P = 1 := by
      rw [show x + 2 * P - y = (x + P - y) + P * 1 by omega, Nat.add_mul_div_left _ _ hP,
        Nat.div_eq_of_lt (by omega)]
    rw [e, e2]
  · simp only [h, ↓reduceIte]
    have e : (x + 2 * P - y) % (2 * P) = x - y := by
      rw [show x + 2 * P - y = (x - y) + 2 * P by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [e, Nat.div_eq_of_lt (by omega)]

theorem val_add_ite (b : ZMod 2) (c : Prop) [Decidable c] :
    (b + if c then 1 else 0).val = (b.val + if c then 1 else 0) % 2 := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]
    rcases bit_cases b with rfl | rfl <;> decide
  · simp only [hc, ↓reduceIte]
    rcases bit_cases b with rfl | rfl <;> decide

/-- The flag bit, the `x` bits and the `y` bits of the basis index: the value of the ideal
permutation computed from the parts. -/
theorem final_arith (k : ℕ) (b : ZMod 2) (X Y : ℕ) (hX : X < 2 ^ k) :
    (b + if X < Y then 1 else 0).val + 2 * (X + 2 ^ k * Y) =
      ((b.val + 2 * (X + 2 ^ k * Y)) % 2 +
        (if (b.val + 2 * (X + 2 ^ k * Y)) / 2 % 2 ^ k < (b.val + 2 * (X + 2 ^ k * Y)) / 2 / 2 ^ k
          then 1 else 0)) % 2 + 2 * ((b.val + 2 * (X + 2 ^ k * Y)) / 2) := by
  have hb : b.val < 2 := ZMod.val_lt b
  have e12 : ∀ Z : ℕ, (b.val + 2 * Z) % 2 = b.val ∧ (b.val + 2 * Z) / 2 = Z := fun Z ↦ by omega
  have e3 : (X + 2 ^ k * Y) % 2 ^ k = X := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hX]
  have e4 : (X + 2 ^ k * Y) / 2 ^ k = Y := by
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hX, zero_add]
  rw [(e12 _).1, (e12 _).2, e3, e4, val_add_ite]

/-- Value of the flag table `lessThanFlag k` on a basis index. -/
theorem lessThanFlag_val (k : ℕ) (u : Fin (2 ^ (2 * k))) :
    (lessThanFlag k u : ℕ) = if (u : ℕ) % 2 ^ k < (u : ℕ) / 2 ^ k then 1 else 0 := by
  have e1 : ((splitEqualBasisEquiv k u).1 : ℕ) = (u : ℕ) / 2 ^ k := by
    simp [splitEqualBasisEquiv, splitBasisEquiv, finProdFinEquiv_symm_apply, Fin.divNat]
  have e2 : ((splitEqualBasisEquiv k u).2 : ℕ) = (u : ℕ) % 2 ^ k := by
    simp [splitEqualBasisEquiv, splitBasisEquiv, finProdFinEquiv_symm_apply, Fin.modNat]
  have hiff : (splitEqualBasisEquiv k u).2 < (splitEqualBasisEquiv k u).1 ↔
      (u : ℕ) % 2 ^ k < (u : ℕ) / 2 ^ k := by rw [Fin.lt_def, e1, e2]
  unfold lessThanFlag
  simp only [hiff]
  split_ifs
  · rfl
  · rfl

/-- Value of `tableAddPerm f` on a basis index with low part `b` and high part `x`. Copied from
`tableAddPerm_val` in the `ControlledAddConstant` baseline, so that each baseline stands alone. -/
theorem tableAddPerm_val {m k : ℕ} (f : Fin (2 ^ m) → Fin (2 ^ k))
    (j : Fin (2 ^ (m + k))) (b : Fin (2 ^ k)) (x : Fin (2 ^ m))
    (hb : j.val % 2 ^ k = b.val) (hx : j.val / 2 ^ k = x.val) :
    ((tableAddPerm f) j : ℕ) = (b.val + (f x).val) % 2 ^ k + 2 ^ k * x.val := by
  have hjx : (Fin.cast (by rw [pow_add]) j).divNat = x :=
    Fin.ext (by simp [Fin.divNat, hx])
  simp [tableAddPerm, splitBasisEquiv, addRightShear, finProdFinEquiv_symm_apply, hjx,
    Fin.modNat, hb, Fin.val_add]

/-- Value of the ideal permutation `tableAddPerm (lessThanFlag k)` on a basis index `j`: the flag is
the lowest bit, flipped by `[x < y]`, where `x` is the next `k` bits and `y` the top `k` bits. -/
theorem comparatorPerm_val (k : ℕ) (j : Fin (2 ^ (2 * k + 1))) :
    ((tableAddPerm (lessThanFlag k)) j : ℕ) =
      ((j : ℕ) % 2 + (if (j : ℕ) / 2 % 2 ^ k < (j : ℕ) / 2 / 2 ^ k then 1 else 0)) % 2 +
        2 * ((j : ℕ) / 2) := by
  have hj : (j : ℕ) < 2 ^ (2 * k) * 2 := lt_of_lt_of_eq j.isLt (pow_succ 2 (2 * k))
  have hx : (j : ℕ) / 2 < 2 ^ (2 * k) := by omega
  have h := tableAddPerm_val (lessThanFlag k) j ⟨(j : ℕ) % 2, by omega⟩ ⟨(j : ℕ) / 2, hx⟩
    (by simp) (by simp)
  rw [lessThanFlag_val] at h
  exact h

/-! ### Step lists -/

theorem noUnxor_rippleSteps : ∀ (K : ℕ) (rA rB : QRegister (K + 1) n) (ci : Wire n)
    (rC : QRegister K n), ∀ s ∈ rippleSteps K rA rB ci rC, s.NoUnxor := by
  intro K
  induction K with
  | zero =>
    intro rA rB ci rC s hs
    simp only [rippleSteps, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> trivial
  | succ K ih =>
    intro rA rB ci rC s hs
    simp only [rippleSteps, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with ((rfl | rfl | rfl | rfl) | hs) | (rfl | rfl | rfl | rfl)
    all_goals first | trivial | exact ih _ _ _ _ s hs

theorem andCount_inv_sum (ss : List (Step n)) :
    ((ss.reverse.map Step.inv).map Step.andCount).sum = (ss.map (Step.andCount ∘ Step.inv)).sum := by
  rw [List.map_map, List.map_reverse, List.sum_reverse]

theorem andCount_inv_rippleSteps_aux : ∀ (K : ℕ) (rA rB : QRegister (K + 1) n) (ci : Wire n)
    (rC : QRegister K n), ((rippleSteps K rA rB ci rC).map (Step.andCount ∘ Step.inv)).sum = K := by
  intro K
  induction K with
  | zero =>
    intro rA rB ci rC
    rfl
  | succ K ih =>
    intro rA rB ci rC
    rw [rippleSteps, List.map_append, List.map_append, List.sum_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp_apply,
      Step.inv, Step.andCount]
    omega

theorem andCount_inv_rippleSteps (K : ℕ) (rA rB : QRegister (K + 1) n) (ci : Wire n)
    (rC : QRegister K n) :
    (((rippleSteps K rA rB ci rC).reverse.map Step.inv).map Step.andCount).sum = K := by
  rw [andCount_inv_sum]
  exact andCount_inv_rippleSteps_aux K rA rB ci rC

/-! ### Register facts -/

/-- Disjointness of slices of disjoint registers. -/
theorem disj_slice {N M : ℕ} (rData : QRegister N n) (rAnc : QRegister M n)
    (h : rData.DisjointWires rAnc) (a b : ℕ) (ha : a + b ≤ N) (a' b' : ℕ) (ha' : a' + b' ≤ M) :
    (rData.slice a b ha).DisjointWires (rAnc.slice a' b' ha') :=
  (h.compose_left _).compose_right _

/-- A slice of one register is disjoint from a wire of a disjoint register. -/
theorem slice_disj_wire {N M : ℕ} (rData : QRegister N n) (rAnc : QRegister M n)
    (h : rData.DisjointWires rAnc) (a b : ℕ) (ha : a + b ≤ N) (j : Fin M) :
    (rData.slice a b ha).DisjointWires (QRegister.singleton (rAnc j)) :=
  QRegister.disjoint_iff.mpr fun i _ ↦ (h.compose_left (QRegister.block a b ha)).ne i j

/-- A wire outside a slice of its register is disjoint from the slice. -/
theorem wire_disj_slice {M : ℕ} (rAnc : QRegister M n) (j : Fin M) (a b : ℕ) (ha : a + b ≤ M)
    (hj : (j : ℕ) < a ∨ a + b ≤ j) :
    (QRegister.singleton (rAnc j)).DisjointWires (rAnc.slice a b ha) :=
  QRegister.disjoint_iff.mpr fun _ i e ↦ apply_not_mem_slice rAnc j a b ha hj ⟨i, e.symm⟩

theorem anc_ne {M : ℕ} (rAnc : QRegister M n) (i j : ℕ) (hi : i < M) (hj : j < M) (h : i ≠ j) :
    rAnc ⟨i, hi⟩ ≠ rAnc ⟨j, hj⟩ := fun e ↦ h (congrArg Fin.val (rAnc.wires.injective e))

theorem anc_not_mem_slice {N M : ℕ} (rData : QRegister N n) (rAnc : QRegister M n)
    (h : rData.DisjointWires rAnc) (a b : ℕ) (ha : a + b ≤ N) (j : Fin M) :
    rAnc j ∉ Set.range (rData.slice a b ha).wires :=
  fun ⟨i, hi⟩ ↦ (h.compose_left (QRegister.block a b ha)).ne i j hi

theorem not_mem_single {a w : Wire n} (h : a ≠ w) : a ∉ Set.range (QRegister.singleton w).wires :=
  fun ⟨_, hi⟩ ↦ h hi.symm

theorem disj_concat_left {k m p : ℕ} {r : QRegister k n} {s : QRegister m n}
    {h : r.DisjointWires s} {u : QRegister p n} (h1 : r.DisjointWires u)
    (h2 : s.DisjointWires u) : (r.concat s h).DisjointWires u := by
  rw [QRegister.disjoint_iff]
  intro i j
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i
  · rw [QRegister.concat_apply_left]
    exact h1.ne i j
  · rw [QRegister.concat_apply_right]
    exact h2.ne i j

theorem disj_concat_right {k m p : ℕ} {r : QRegister k n} {s : QRegister m n}
    {h : r.DisjointWires s} {u : QRegister p n} (h1 : u.DisjointWires r)
    (h2 : u.DisjointWires s) : u.DisjointWires (r.concat s h) :=
  QRegister.disjoint_comm.mp
    (disj_concat_left (QRegister.disjoint_comm.mp h1) (QRegister.disjoint_comm.mp h2))

theorem not_mem_concat {k m : ℕ} {r : QRegister k n} {s : QRegister m n} {h : r.DisjointWires s}
    {w : Wire n} (h1 : w ∉ Set.range r.wires) (h2 : w ∉ Set.range s.wires) :
    w ∉ Set.range (r.concat s h).wires := by
  rintro ⟨i, hi⟩
  revert hi
  refine Fin.addCases (fun i hi ↦ ?_) (fun i hi ↦ ?_) i
  · rw [QRegister.concat_apply_left] at hi
    exact h1 ⟨i, hi⟩
  · rw [QRegister.concat_apply_right] at hi
    exact h2 ⟨i, hi⟩

/-- The value read from a register extended by one wire. -/
theorem localIdx_concat_single {k : ℕ} (r : QRegister k n) (w : Wire n)
    (h : r.DisjointWires (QRegister.singleton w)) (β : BitAssignment n) :
    (localIdx (r.concat (QRegister.singleton w) h) β : ℕ) =
      (localIdx r β : ℕ) + 2 ^ k * (β w).val := by
  rw [localIdx_val, localIdx_val, Fin.sum_univ_add, Fin.sum_univ_one]
  simp only [QRegister.concat_apply_left, QRegister.concat_apply_right,
    QRegister.singleton_apply, Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero, add_zero]
  ring

/-- The number read from the data register: the flag bit, then `x`, then `y`. -/
theorem localIdx_cmpData (k : ℕ) (rData : QRegister (2 * k + 1) n) (β : BitAssignment n) :
    (localIdx rData β : ℕ) = (β (rData ⟨0, by omega⟩)).val +
      2 * ((localIdx (rData.slice 1 k (by omega)) β : ℕ) +
        2 ^ k * (localIdx (rData.slice (1 + k) k (by omega)) β : ℕ)) := by
  have h0 : (localIdx (rData.slice 0 1 (by omega)) β : ℕ) = (β (rData ⟨0, by omega⟩)).val := by
    rw [localIdx_val, Fin.sum_univ_one]
    have e : rData.slice 0 1 (by omega) 0 = rData ⟨0, by omega⟩ := by
      rw [QRegister.slice_apply]
      rfl
    rw [e]
    simp
  rw [localIdx_val_split rData 1 (2 * k) (by omega),
    localIdx_val_split (rData.slice 1 (2 * k) (by omega)) k k (by omega), h0]
  simp only [localIdx_slice_slice, add_zero, pow_one]

/-! ### The circuit -/

/-- The `y` bits extended by the clean ancilla wire `rAnc 1`. -/
abbrev extA (k : ℕ) (rData : QRegister (2 * k + 1) n) (rAnc : QRegister (k + 3) n)
    (h : rData.DisjointWires rAnc) : QRegister (k + 1) n :=
  (rData.slice (1 + k) k (by omega)).concat (QRegister.singleton (rAnc ⟨1, by omega⟩))
    (slice_disj_wire rData rAnc h _ _ _ _)

/-- The `x` bits extended by the clean ancilla wire `rAnc 0`, which receives the borrow. -/
abbrev extB (k : ℕ) (rData : QRegister (2 * k + 1) n) (rAnc : QRegister (k + 3) n)
    (h : rData.DisjointWires rAnc) : QRegister (k + 1) n :=
  (rData.slice 1 k (by omega)).concat (QRegister.singleton (rAnc ⟨0, by omega⟩))
    (slice_disj_wire rData rAnc h _ _ _ _)

/-- The ripple-carry adder `B ↦ A + B` on the extended registers, with carry-in wire `rAnc 2` and
carry wires `rAnc[3, k + 3)`. -/
abbrev comparatorRipple (k : ℕ) (rData : QRegister (2 * k + 1) n) (rAnc : QRegister (k + 3) n)
    (h : rData.DisjointWires rAnc) : List (Step n) :=
  rippleSteps k (extA k rData rAnc h) (extB k rData rAnc h) (rAnc ⟨2, by omega⟩)
    (rAnc.slice 3 k (by omega))

/-- Step list of the comparator on `k` bits: subtract `y` from `x` (the inverse of the adder), copy
the borrow bit to the flag, and add `y` back. Overlapping registers get the empty list. -/
def comparatorSteps (k : ℕ) (rData : QRegister (2 * k + 1) n) (rAnc : QRegister (k + 3) n) :
    List (Step n) :=
  if h : rData.DisjointWires rAnc then
    (comparatorRipple k rData rAnc h).reverse.map Step.inv ++
      [cnot (extB k rData rAnc h (Fin.last k)) (rData ⟨0, by omega⟩)] ++
      comparatorRipple k rData rAnc h
  else []

theorem andCount_comparatorSteps (k : ℕ) (rData : QRegister (2 * k + 1) n)
    (rAnc : QRegister (k + 3) n) :
    ((comparatorSteps k rData rAnc).map Step.andCount).sum ≤ 2 * k := by
  unfold comparatorSteps
  split_ifs with h
  · rw [List.map_append, List.map_append, List.sum_append, List.sum_append,
      andCount_inv_rippleSteps, andCount_rippleSteps]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Step.andCount]
    omega
  · simp

/-- The core of the comparator on abstract registers: the inverse ripple, a `CNOT` of the top bit of
`B` onto `t`, then the ripple again, flips `t` by `[x < y]` and changes nothing else. -/
theorem runList_comparatorCore (K : ℕ) (rA rB : QRegister (K + 1) n) (rC : QRegister K n)
    (ci t : Wire n) (hAB : rA.DisjointWires rB) (hAC : rA.DisjointWires rC)
    (hBC : rB.DisjointWires rC) (hciA : ci ∉ Set.range rA.wires) (hciB : ci ∉ Set.range rB.wires)
    (hciC : ci ∉ Set.range rC.wires) (htA : t ∉ Set.range rA.wires)
    (htB : t ∉ Set.range rB.wires) (htC : t ∉ Set.range rC.wires) (htci : t ≠ ci)
    (β : BitAssignment n) (hclean : ∀ i, β (rC i) = 0) (hci : β ci = 0)
    (x y : ℕ) (hx : (localIdx rB β : ℕ) = x) (hy : (localIdx rA β : ℕ) = y)
    (hxl : x < 2 ^ K) (hyl : y < 2 ^ K) :
    runList ((rippleSteps K rA rB ci rC).reverse.map Step.inv ++
        [cnot (rB (Fin.last K)) t] ++ rippleSteps K rA rB ci rC) β =
      some (update β t (β t + if x < y then 1 else 0)) := by
  have hM2 : 2 ^ (K + 1) = 2 * 2 ^ K := by ring
  have hP : 0 < 2 ^ K := by positivity
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = (x + 2 * 2 ^ K - y) % (2 * 2 ^ K) := ⟨_, rfl⟩
  have hdlt : d < 2 ^ (K + 1) := by
    rw [hd, hM2]
    exact Nat.mod_lt _ (by positivity)
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀, β₀ = writeReg β rB (basisBits (K + 1) ⟨d, hdlt⟩) := ⟨_, rfl⟩
  have hβ₀A : localIdx rA β₀ = localIdx rA β := by
    rw [hβ₀]
    exact localIdx_writeReg_of_disjoint β rB rA (QRegister.disjoint_comm.mp hAB) _
  have hβ₀B : (localIdx rB β₀ : ℕ) = d := by
    rw [hβ₀, localIdx_writeReg, basisBitsEquiv_symm_basisBits]
  have hβ₀ci : β₀ ci = 0 := by
    rw [hβ₀, writeReg_apply_of_not_mem _ _ _ _ hciB]
    exact hci
  have hβ₀t : β₀ t = β t := by
    rw [hβ₀, writeReg_apply_of_not_mem _ _ _ _ htB]
  have hβ₀C : ∀ i, β₀ (rC i) = 0 := fun i ↦ by
    rw [hβ₀, writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint (QRegister.disjoint_comm.mp hBC) i)]
    exact hclean i
  -- writing back the original value of `B` undoes the subtraction
  have key : ∀ (m : ℕ) (hm : m < 2 ^ (K + 1)), m = x →
      writeReg β₀ rB (basisBits (K + 1) ⟨m, hm⟩) = β := by
    intro m hm hmx
    have hF : (⟨m, hm⟩ : Fin (2 ^ (K + 1))) = localIdx rB β := Fin.ext (by
      show m = _
      rw [hmx, hx])
    rw [hF, hβ₀, writeReg_writeReg, basisBits_basisBitsEquiv_symm, writeReg_self]
  have hidx : ((localIdx rA β₀ : ℕ) + (localIdx rB β₀ : ℕ) + (β₀ ci).val) % 2 ^ (K + 1) = x := by
    rw [hβ₀A, hβ₀B, hβ₀ci, hy, ZMod.val_zero, add_zero, hM2, hd]
    exact sub_arith (2 ^ K) x y hxl hyl
  have hR0 : runList (rippleSteps K rA rB ci rC) β₀ = some β := by
    rw [runList_rippleSteps K rA rB ci rC hAB hAC hBC hciA hciB hciC β₀ hβ₀C]
    exact congrArg some (key _ (Nat.mod_lt _ (by positivity)) hidx)
  have hrev : runList ((rippleSteps K rA rB ci rC).reverse.map Step.inv) β = some β₀ :=
    runList_inv (noUnxor_rippleSteps K rA rB ci rC) hR0
  -- the borrow bit
  have hbit : d / 2 ^ K % 2 = if x < y then 1 else 0 := by
    rw [hd]
    exact borrow_arith (2 ^ K) x y hP hxl hyl
  have hflag : β₀ (rB (Fin.last K)) = if x < y then 1 else 0 := by
    rw [hβ₀, writeReg_apply_reg, basisBits_mk_apply, Fin.val_last, hbit]
    split_ifs <;> simp
  obtain ⟨w, hw⟩ : ∃ w, w = β₀ t + β₀ (rB (Fin.last K)) := ⟨_, rfl⟩
  have hw' : w = β t + if x < y then 1 else 0 := by rw [hw, hβ₀t, hflag]
  have hex : rB (Fin.last K) ≠ t := fun h ↦ htB ⟨Fin.last K, h⟩
  have hcn : runList [cnot (rB (Fin.last K)) t] β₀ = some (update β₀ t w) := by
    rw [hw]
    simp only [runList_cons, runList_nil, Step.run, ite_eq_left hex, Option.bind_some]
  have hβ₁C : ∀ i, update β₀ t w (rC i) = 0 := fun i ↦ by
    rw [update_of_ne (fun h ↦ htC ⟨i, h⟩)]
    exact hβ₀C i
  have hidx₁ : ((localIdx rA (update β₀ t w) : ℕ) + (localIdx rB (update β₀ t w) : ℕ) +
      (update β₀ t w ci).val) % 2 ^ (K + 1) = x := by
    rw [localIdx_update_of_not_mem rA β₀ htA, localIdx_update_of_not_mem rB β₀ htB,
      update_of_ne (Ne.symm htci)]
    exact hidx
  have hR1 := runList_rippleSteps K rA rB ci rC hAB hAC hBC hciA hciB hciC (update β₀ t w) hβ₁C
  rw [runList_append, runList_append, hrev, Option.bind_some, hcn, Option.bind_some, hR1]
  refine congrArg some ?_
  rw [← hw', writeReg_update_of_not_mem _ _ _ htB, key _ (Nat.mod_lt _ (by positivity)) hidx₁]

/-- The comparator step list computes `|y⟩|x⟩|t⟩ ↦ |y⟩|x⟩|t ⊕ [x < y]⟩` on clean ancillas. -/
theorem runList_comparatorSteps (k : ℕ) (rData : QRegister (2 * k + 1) n)
    (rAnc : QRegister (k + 3) n) (hdisj : rData.DisjointWires rAnc)
    (σ : Equiv.Perm (Fin (2 ^ (2 * k + 1))))
    (hσ : ∀ j : Fin (2 ^ (2 * k + 1)), (σ j : ℕ) =
      ((j : ℕ) % 2 + (if (j : ℕ) / 2 % 2 ^ k < (j : ℕ) / 2 / 2 ^ k then 1 else 0)) % 2 +
        2 * ((j : ℕ) / 2))
    (β : BitAssignment n) (hβ : localIdx rAnc β = 0) :
    runList (comparatorSteps k rData rAnc) β =
      some (writeReg β rData (basisBits (2 * k + 1) (σ (localIdx rData β)))) := by
  have hclean := eq_zero_of_localIdx_eq_zero rAnc β hβ
  have hXY : (rData.slice 1 k (by omega)).DisjointWires (rData.slice (1 + k) k (by omega)) :=
    QRegister.slice_disjoint_of_le rData 1 k (1 + k) k (by omega) (by omega) (by omega)
  have hAB : (extA k rData rAnc hdisj).DisjointWires (extB k rData rAnc hdisj) :=
    disj_concat_left
      (disj_concat_right (QRegister.disjoint_comm.mp hXY)
        (slice_disj_wire rData rAnc hdisj _ _ _ ⟨0, by omega⟩))
      (disj_concat_right
        (QRegister.disjoint_comm.mp (slice_disj_wire rData rAnc hdisj 1 k (by omega) ⟨1, by omega⟩))
        (QRegister.singleton_disjoint (anc_ne rAnc 1 0 (by omega) (by omega) (by omega))))
  have hAC : (extA k rData rAnc hdisj).DisjointWires (rAnc.slice 3 k (by omega)) :=
    disj_concat_left (disj_slice rData rAnc hdisj _ _ _ _ _ _)
      (wire_disj_slice rAnc ⟨1, by omega⟩ 3 k (by omega) (Or.inl (show 1 < 3 by omega)))
  have hBC : (extB k rData rAnc hdisj).DisjointWires (rAnc.slice 3 k (by omega)) :=
    disj_concat_left (disj_slice rData rAnc hdisj _ _ _ _ _ _)
      (wire_disj_slice rAnc ⟨0, by omega⟩ 3 k (by omega) (Or.inl (by dsimp; omega)))
  have hciA : rAnc ⟨2, by omega⟩ ∉ Set.range (extA k rData rAnc hdisj).wires :=
    not_mem_concat (anc_not_mem_slice rData rAnc hdisj _ _ _ _)
      (not_mem_single (anc_ne rAnc 2 1 (by omega) (by omega) (by omega)))
  have hciB : rAnc ⟨2, by omega⟩ ∉ Set.range (extB k rData rAnc hdisj).wires :=
    not_mem_concat (anc_not_mem_slice rData rAnc hdisj _ _ _ _)
      (not_mem_single (anc_ne rAnc 2 0 (by omega) (by omega) (by omega)))
  have hciC : rAnc ⟨2, by omega⟩ ∉ Set.range (rAnc.slice 3 k (by omega)).wires :=
    apply_not_mem_slice rAnc _ 3 k (by omega) (Or.inl (by dsimp; omega))
  have htA : rData ⟨0, by omega⟩ ∉ Set.range (extA k rData rAnc hdisj).wires :=
    not_mem_concat (apply_not_mem_slice rData _ (1 + k) k (by omega) (Or.inl (by dsimp; omega)))
      (not_mem_single (hdisj.ne _ ⟨1, by omega⟩))
  have htB : rData ⟨0, by omega⟩ ∉ Set.range (extB k rData rAnc hdisj).wires :=
    not_mem_concat (apply_not_mem_slice rData _ 1 k (by omega) (Or.inl (by dsimp; omega)))
      (not_mem_single (hdisj.ne _ ⟨0, by omega⟩))
  have htC : rData ⟨0, by omega⟩ ∉ Set.range (rAnc.slice 3 k (by omega)).wires :=
    not_mem_of_disjoint (hdisj.compose_right (QRegister.block 3 k (by omega))) ⟨0, by omega⟩
  have hx : (localIdx (extB k rData rAnc hdisj) β : ℕ) =
      (localIdx (rData.slice 1 k (by omega)) β : ℕ) := by
    rw [localIdx_concat_single, hclean, ZMod.val_zero, mul_zero, add_zero]
  have hy : (localIdx (extA k rData rAnc hdisj) β : ℕ) =
      (localIdx (rData.slice (1 + k) k (by omega)) β : ℕ) := by
    rw [localIdx_concat_single, hclean, ZMod.val_zero, mul_zero, add_zero]
  have core := runList_comparatorCore k (extA k rData rAnc hdisj) (extB k rData rAnc hdisj)
    (rAnc.slice 3 k (by omega)) (rAnc ⟨2, by omega⟩) (rData ⟨0, by omega⟩) hAB hAC hBC hciA hciB
    hciC htA htB htC (hdisj.ne _ _) β (fun _ ↦ hclean _) (hclean _) _ _ hx hy
    (localIdx (rData.slice 1 k (by omega)) β).isLt
    (localIdx (rData.slice (1 + k) k (by omega)) β).isLt
  simp only [comparatorSteps, hdisj, ↓reduceDIte]
  rw [core]
  refine congrArg some ?_
  rw [← writeReg_eq_of_eqOn β (update β (rData ⟨0, by omega⟩) _) rData fun w hw ↦
    update_of_ne (fun e ↦ hw ⟨⟨0, by omega⟩, e.symm⟩) _ _]
  congr 1
  rw [← basisBits_basisBitsEquiv_symm (2 * k + 1) (fun p ↦ _)]
  congr 1
  apply Fin.ext
  have hL : ∀ γ : BitAssignment n,
      ((basisBits (2 * k + 1)).symm (fun p ↦ γ (rData p)) : Fin _) = localIdx rData γ :=
    fun _ ↦ rfl
  have hXS := localIdx_update_of_not_mem (rData.slice 1 k (by omega)) β
    (apply_not_mem_slice rData ⟨0, by omega⟩ 1 k (by omega) (Or.inl (by dsimp; omega)))
    (β (rData ⟨0, by omega⟩) + if (localIdx (rData.slice 1 k (by omega)) β : ℕ) <
      (localIdx (rData.slice (1 + k) k (by omega)) β : ℕ) then 1 else 0)
  have hYS := localIdx_update_of_not_mem (rData.slice (1 + k) k (by omega)) β
    (apply_not_mem_slice rData ⟨0, by omega⟩ (1 + k) k (by omega) (Or.inl (by dsimp; omega)))
    (β (rData ⟨0, by omega⟩) + if (localIdx (rData.slice 1 k (by omega)) β : ℕ) <
      (localIdx (rData.slice (1 + k) k (by omega)) β : ℕ) then 1 else 0)
  rw [hL, hσ, localIdx_cmpData k rData (update β _ _), localIdx_cmpData k rData β, update_self,
    hXS, hYS]
  exact final_arith k _ _ _ (localIdx (rData.slice 1 k (by omega)) β).isLt

end ComparatorImpl

open ArcsinImpl ArcsinImpl.Step

/-- Number of clean ancilla qubits `comparatorProgram` uses at bit-width `k`. -/
def comparatorAncillas (k : ℕ) : ℕ := k + 3

/-- Parameterized comparator on `2 * k + 1` data wires `rData` (the flag wire `t`, followed by `k`
wires `x` and then `k` wires `y`, each least-significant bit first) and `comparatorAncillas k` clean
ancilla wires `rAnc`. -/
def comparatorProgram {n : ℕ} (k : ℕ)
    (rData : QRegister (2 * k + 1) n)
    (rAnc : QRegister (comparatorAncillas k) n) : DynamicCircuit Var n :=
  compileList v (ComparatorImpl.comparatorSteps k rData rAnc)

/-- Parameterized correctness theorem: for every bit-width `k`, `comparatorProgram k` realizes
`comparatorUnitary k` as an exact clean subroutine across all disjoint register placements. -/
theorem comparator_correctness (k : ℕ) :
    ∀ {n : ℕ}
      (rData : QRegister (2 * k + 1) n)
      (rAnc : QRegister (comparatorAncillas k) n)
      (hdisj : rData.DisjointWires rAnc),
      RealizesCleanSubroutine rData rAnc hdisj (comparatorUnitary k)
        (comparatorProgram k rData rAnc).compile := by
  intro n rData rAnc hdisj
  refine realizesCleanSubroutine_compileList v _ rData rAnc hdisj
    (tableAddPerm (lessThanFlag k)) fun β hβ ↦ ?_
  exact ComparatorImpl.runList_comparatorSteps k rData rAnc hdisj _
    (fun j ↦ ComparatorImpl.comparatorPerm_val k j) β hβ

/-- `T`-gate count of `comparatorProgram k`, which the cost predicates require to use no `TOFF`
gates. -/
abbrev comparatorTCount {n : ℕ} (k : ℕ)
    (rData : QRegister (2 * k + 1) n)
    (rAnc : QRegister (comparatorAncillas k) n) : ℕ :=
  (comparatorProgram k rData rAnc).count PrimitiveGate.T

/-- Spacetime cost `T count * qubits` of `comparatorProgram k`, counting all
`2 * k + 1 + comparatorAncillas k` data and clean ancilla qubits. -/
abbrev comparatorSpacetime {n : ℕ} (k : ℕ)
    (rData : QRegister (2 * k + 1) n)
    (rAnc : QRegister (comparatorAncillas k) n) : ℕ :=
  comparatorTCount k rData rAnc * (2 * k + 1 + comparatorAncillas k)

/-!
## Cost Predicates

Both predicates forbid primitive `TOFF` gates (so every Toffoli must be decomposed into Clifford +
`T` + measurements) and bound a cost of `comparatorProgram` at bit-width `k` across all register
placements.
-/

/-- `comparatorProgram` at bit-width `k` uses no primitive `TOFF` gates and has `T` count at most
`cost`, across all register placements. -/
abbrev SatisfiesComparatorTBound (k cost : ℕ) : Prop :=
  ∀ {n : ℕ}
    (rData : QRegister (2 * k + 1) n)
    (rAnc : QRegister (comparatorAncillas k) n),
    (comparatorProgram k rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      comparatorTCount k rData rAnc ≤ cost

/-- `comparatorProgram` at bit-width `k` uses no primitive `TOFF` gates and has spacetime cost at
most `cost`, for every constant and register placement it can be given. -/
abbrev SatisfiesComparatorSpacetimeBound (k cost : ℕ) : Prop :=
  ∀ {n : ℕ}
    (rData : QRegister (2 * k + 1) n)
    (rAnc : QRegister (comparatorAncillas k) n),
    (comparatorProgram k rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      comparatorSpacetime k rData rAnc ≤ cost

/-- The baseline uses no `TOFF` gates and at most `8 * k` `T` gates. -/
theorem comparator_baseline_t_bound (k : ℕ) : SatisfiesComparatorTBound k (8 * k) := by
  intro n rData rAnc
  refine ⟨count_TOFF_compileList v _, ?_⟩
  have h := count_T_compileList v (ComparatorImpl.comparatorSteps k rData rAnc)
  have h2 := ComparatorImpl.andCount_comparatorSteps k rData rAnc
  refine le_trans h ?_
  omega

/-- The baseline has spacetime cost at most `8 * k * (2 * k + 1 + (k + 3))`. -/
theorem comparator_baseline_spacetime_bound (k : ℕ) :
    SatisfiesComparatorSpacetimeBound k (8 * k * (2 * k + 1 + (k + 3))) := by
  intro n rData rAnc
  exact ⟨(comparator_baseline_t_bound k rData rAnc).1,
    Nat.mul_le_mul_right _ (comparator_baseline_t_bound k rData rAnc).2⟩

/-!
## Cost Theorems at Every Bit-Width
-/

/-- Claimed `T` count of `comparatorProgram`, as a function of the bit-width `k`. -/
def comparatorTCost (k : ℕ) : ℕ := 8 * k

theorem comparator_t_cost (k : ℕ) :
    SatisfiesComparatorTBound k (comparatorTCost k) :=
  comparator_baseline_t_bound k

/-- Claimed spacetime cost of `comparatorProgram`, as a function of the bit-width `k`. -/
def comparatorSpacetimeCost (k : ℕ) : ℕ := 8 * k * (2 * k + 1 + (k + 3))

theorem comparator_spacetime_cost (k : ℕ) :
    SatisfiesComparatorSpacetimeBound k (comparatorSpacetimeCost k) :=
  comparator_baseline_spacetime_bound k

/-!
## Cost Theorems at the Pinned Bit-Widths `k = 64` and `k = 2048`
-/

/-- Claimed `T` count bound for `comparatorProgram` at `k = 64`. -/
def comparatorK64TCost : ℕ := 512

theorem comparator_k64_t_cost :
    SatisfiesComparatorTBound 64 comparatorK64TCost :=
  comparator_baseline_t_bound 64

/-- Claimed spacetime cost bound for `comparatorProgram` at `k = 64`. -/
def comparatorK64SpacetimeCost : ℕ := 100352

theorem comparator_k64_spacetime_cost :
    SatisfiesComparatorSpacetimeBound 64 comparatorK64SpacetimeCost :=
  comparator_baseline_spacetime_bound 64

/-- Claimed `T` count bound for `comparatorProgram` at `k = 2048`. -/
def comparatorK2048TCost : ℕ := 16384

theorem comparator_k2048_t_cost :
    SatisfiesComparatorTBound 2048 comparatorK2048TCost :=
  comparator_baseline_t_bound 2048

/-- Claimed spacetime cost bound for `comparatorProgram` at `k = 2048`. -/
def comparatorK2048SpacetimeCost : ℕ := 100728832

theorem comparator_k2048_spacetime_cost :
    SatisfiesComparatorSpacetimeBound 2048 comparatorK2048SpacetimeCost :=
  comparator_baseline_spacetime_bound 2048

end QuantumComputation.Specs
