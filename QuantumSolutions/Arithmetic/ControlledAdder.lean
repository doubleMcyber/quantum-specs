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
# Controlled In-Place Addition (`controlledAdder`) Specification: Baseline Solution

Baseline: compute the product `c * x_i` of the control and each addend bit into `k` clean ancilla
wires with temporary ANDs (`and4t`), add that register into the target with the ripple-carry adder
`ArcsinImpl.rippleSteps` of the `arcsin` solution in `QuantumComputationDiscoveries`, and return the
product register to zero by measurement (`unand`). It uses `2 * k` clean ancillas (`k` product
wires, one zero carry-in wire and `k - 1` carry wires) and at most `4 * k + 4 * (k - 1)` `T` gates.
The specification text below is unchanged; only the holes are filled and the theorems proved.

Parameterized specification for reversible in-place addition of two `k`-bit quantum registers
controlled on one qubit, `|c⟩|x⟩|b⟩|0⟩^⊗m ↦ |c⟩|x⟩|(b + c * x) mod 2^k⟩|0⟩^⊗m`, for every bit-width
`k`. Both registers hold unsigned integers in `[0, 2^k)`, least-significant bit first. The control
`c` and the addend `x` are preserved, the target `b` is overwritten by the sum modulo `2^k` when
`c = 1` and is unchanged when `c = 0`, and the `m` clean ancilla qubits are returned to zero. Kets
are written with the most significant register on the left, so the rightmost register occupies the
lowest wires.

There are two resource metrics over Clifford + `T` with measurements: the `T` count, and spacetime
(`T count * qubits`), where `qubits = 1 + k + k + controlledAdderAncillas k` is the total number of
data and clean ancilla qubits. Each metric has three cost theorems. One bounds the cost at every
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
## Reversible Controlled-Addition Unitary
-/

/-- The controlled addend `c * x` as a table on a `(1 + k)`-qubit basis index, which
`splitBasisEquiv` splits into the control `c` (highest bit) and the addend `x` (low `k` bits). -/
def controlledAddend (k : ℕ) (u : Fin (2 ^ (1 + k))) : Fin (2 ^ k) :=
  if (splitBasisEquiv 1 k u).1 = 1 then (splitBasisEquiv 1 k u).2 else 0

/-- Ideal `(1 + 2k)`-qubit unitary `|c⟩|x⟩|b⟩ ↦ |c⟩|x⟩|(b + c * x) mod 2^k⟩`: the basis permutation
`tableAddPerm` of `controlledAddend`, with the target `b` as the low `k` bits of the basis index. -/
noncomputable abbrev controlledAdderUnitary (k : ℕ) : Unitary (2 ^ (1 + k + k)) :=
  permutationUnitary (tableAddPerm (controlledAddend k))

/-!
## Candidate Program & Correctness
-/

/-- By default we allow only a single variable. -/
inductive ControlledAdder.Var where | v deriving DecidableEq, Inhabited

open ControlledAdder (Var)
open ControlledAdder.Var (v)

/-!
## Baseline Construction
-/

namespace ControlledAdderImpl

open ArcsinImpl ArcsinImpl.Step Function

variable {n : ℕ}

/-- Value of `tableAddPerm (controlledAddend k)` on a basis index `j`: the target is the low `k`
bits, the addend the next `k` bits and the control the top bit. -/
theorem controlledAddPerm_val (k : ℕ) (j : Fin (2 ^ (1 + k + k))) :
    ((tableAddPerm (controlledAddend k)) j : ℕ) =
      ((j : ℕ) % 2 ^ k + (if (j : ℕ) / 2 ^ k / 2 ^ k = 1 then (j : ℕ) / 2 ^ k % 2 ^ k else 0)) %
        2 ^ k + 2 ^ k * ((j : ℕ) / 2 ^ k) := by
  simp [tableAddPerm, controlledAddend, splitBasisEquiv, addRightShear,
    finProdFinEquiv_symm_apply, Fin.modNat, Fin.divNat, Fin.val_add, Fin.ext_iff]
  split_ifs <;> simp

theorem controlled_arith (k b x cv : ℕ) (hb : b < 2 ^ k) (hx : x < 2 ^ k) :
    ((b + 2 ^ k * (x + 2 ^ k * cv)) % 2 ^ k +
        (if (b + 2 ^ k * (x + 2 ^ k * cv)) / 2 ^ k / 2 ^ k = 1 then
          (b + 2 ^ k * (x + 2 ^ k * cv)) / 2 ^ k % 2 ^ k else 0)) % 2 ^ k +
      2 ^ k * ((b + 2 ^ k * (x + 2 ^ k * cv)) / 2 ^ k) =
    ((if cv = 1 then x else 0) + b + 0) % 2 ^ k + 2 ^ k * (x + 2 ^ k * cv) := by
  have h2 : 0 < 2 ^ k := by positivity
  have e1 : (b + 2 ^ k * (x + 2 ^ k * cv)) % 2 ^ k = b := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  have e2 : (b + 2 ^ k * (x + 2 ^ k * cv)) / 2 ^ k = x + 2 ^ k * cv := by
    rw [Nat.add_mul_div_left _ _ h2, Nat.div_eq_of_lt hb, zero_add]
  have e3 : (x + 2 ^ k * cv) / 2 ^ k = cv := by
    rw [Nat.add_mul_div_left _ _ h2, Nat.div_eq_of_lt hx, zero_add]
  have e4 : (x + 2 ^ k * cv) % 2 ^ k = x := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  rw [e1, e2, e3, e4, Nat.add_zero, Nat.add_comm b]

/-- Steps computing `c * x_i` into the clean wire `rY i`, for every `i`. -/
def andSteps (c : Wire n) : (w : ℕ) → QRegister w n → QRegister w n → List (Step n)
  | 0, _, _ => []
  | w + 1, rX, rY => and4t c (rX 0) (rY 0) :: andSteps c w (regTail rX) (regTail rY)

/-- Steps returning `rY i = c * x_i` to zero by measurement. -/
def unandSteps (c : Wire n) : (w : ℕ) → QRegister w n → QRegister w n → List (Step n)
  | 0, _, _ => []
  | w + 1, rX, rY => unand c (rX 0) (rY 0) :: unandSteps c w (regTail rX) (regTail rY)

theorem andCount_andSteps (c : Wire n) (w : ℕ) (rX rY : QRegister w n) :
    ((andSteps c w rX rY).map Step.andCount).sum = w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    rw [andSteps, List.map_cons, List.sum_cons, ih (regTail rX) (regTail rY)]
    show 1 + w = w + 1
    omega

theorem andCount_unandSteps (c : Wire n) (w : ℕ) (rX rY : QRegister w n) :
    ((unandSteps c w rX rY).map Step.andCount).sum = 0 := by
  induction w with
  | zero => rfl
  | succ w ih =>
    rw [unandSteps, List.map_cons, List.sum_cons, ih (regTail rX) (regTail rY)]
    rfl

theorem runList_andSteps (c : Wire n) (w : ℕ) (rX rY : QRegister w n)
    (hXY : rX.DisjointWires rY) (hcX : c ∉ Set.range rX.wires) (hcY : c ∉ Set.range rY.wires)
    (β : BitAssignment n) (hclean : ∀ i, β (rY i) = 0) :
    runList (andSteps c w rX rY) β = some (writeReg β rY (fun i ↦ β c * β (rX i))) := by
  induction w generalizing β with
  | zero =>
    rw [andSteps, runList_nil, show (fun i : Fin 0 ↦ β c * β (rX i)) = fun i ↦ β (rY i) from
      funext fun i ↦ i.elim0, writeReg_self]
  | succ w ih =>
    have h1 : c ≠ rX 0 := fun h ↦ hcX ⟨0, h.symm⟩
    have h2 : c ≠ rY 0 := fun h ↦ hcY ⟨0, h.symm⟩
    have h3 : rX 0 ≠ rY 0 := hXY.ne 0 0
    have hstep : (and4t c (rX 0) (rY 0)).run β = some (update β (rY 0) (β c * β (rX 0))) := by
      simp only [Step.run, ite_eq_left (And.intro h1 (And.intro h2 h3)), ite_eq_left (hclean 0)]
    have hβ' : ∀ i, update β (rY 0) (β c * β (rX 0)) (regTail rY i) = 0 := fun i ↦ by
      rw [update_of_ne (regTail_ne_zero rY i), regTail_apply]
      exact hclean _
    rw [andSteps, runList_cons, hstep, Option.bind_some,
      ih (regTail rX) (regTail rY) ((hXY.compose_left _).compose_right _) (not_mem_regTail hcX)
        (not_mem_regTail hcY) _ hβ',
      writeReg_succ β rY, writeReg_update_of_not_mem _ _ _ (zero_not_mem_regTail rY)]
    congr 3
    funext i
    rw [update_of_ne h2, update_of_ne (by rw [regTail_apply]; exact hXY.ne _ _), regTail_apply]

theorem runList_unandSteps (c : Wire n) (w : ℕ) (rX rY : QRegister w n)
    (hXY : rX.DisjointWires rY) (hcX : c ∉ Set.range rX.wires) (hcY : c ∉ Set.range rY.wires)
    (β : BitAssignment n) (hv : ∀ i, β (rY i) = β c * β (rX i)) :
    runList (unandSteps c w rX rY) β = some (writeReg β rY (fun _ ↦ 0)) := by
  induction w generalizing β with
  | zero =>
    rw [unandSteps, runList_nil, show (fun _ : Fin 0 ↦ (0 : ZMod 2)) = fun i ↦ β (rY i) from
      funext fun i ↦ i.elim0, writeReg_self]
  | succ w ih =>
    have h1 : c ≠ rX 0 := fun h ↦ hcX ⟨0, h.symm⟩
    have h2 : c ≠ rY 0 := fun h ↦ hcY ⟨0, h.symm⟩
    have h3 : rX 0 ≠ rY 0 := hXY.ne 0 0
    have hstep : (unand c (rX 0) (rY 0)).run β = some (update β (rY 0) 0) := by
      simp only [Step.run, ite_eq_left (And.intro h1 (And.intro h2 h3)), ite_eq_left (hv 0)]
    have hβ' : ∀ i, update β (rY 0) 0 (regTail rY i) =
        update β (rY 0) 0 c * update β (rY 0) 0 (regTail rX i) := fun i ↦ by
      rw [update_of_ne (regTail_ne_zero rY i), update_of_ne h2,
        update_of_ne (by rw [regTail_apply]; exact hXY.ne _ _), regTail_apply, regTail_apply]
      exact hv _
    rw [unandSteps, runList_cons, hstep, Option.bind_some,
      ih (regTail rX) (regTail rY) ((hXY.compose_left _).compose_right _) (not_mem_regTail hcX)
        (not_mem_regTail hcY) _ hβ',
      writeReg_succ β rY, writeReg_update_of_not_mem _ _ _ (zero_not_mem_regTail rY)]

/-- The number read from `rY` after `andSteps` is `x` if `c = 1` and `0` otherwise. -/
theorem localIdx_andSteps (c : Wire n) (w : ℕ) (rX rY : QRegister w n) (β : BitAssignment n) :
    (localIdx rY (writeReg β rY (fun i ↦ β c * β (rX i))) : ℕ) =
      if (β c).val = 1 then (localIdx rX β : ℕ) else 0 := by
  rw [localIdx_writeReg]
  rcases bit_cases (β c) with h | h
  · have hv : (β c).val = 0 := by rw [h]; rfl
    rw [ite_eq_right (by rw [hv]; exact zero_ne_one)]
    have hf : (fun i : Fin w ↦ β c * β (rX i)) = 0 := funext fun i ↦ by rw [h, zero_mul]; rfl
    rw [hf, basisBits_symm_zero]
    rfl
  · have hv : (β c).val = 1 := by rw [h]; rfl
    rw [ite_eq_left hv]
    simp only [h, one_mul]

/-- Writing `rY` and then clearing it is the identity when `rY` is clean, whatever is written to the
disjoint register `rB` in between. -/
theorem writeReg_chain {w m : ℕ} (β : BitAssignment n) (rY : QRegister w n) (rB : QRegister m n)
    (hBY : rB.DisjointWires rY) (f : BitAssignment w) (g : BitAssignment m)
    (hclean : ∀ i, β (rY i) = 0) :
    writeReg (writeReg (writeReg β rY f) rB g) rY (fun _ ↦ 0) = writeReg β rB g := by
  rw [writeReg_comm _ rB rY hBY g (fun _ ↦ 0), writeReg_writeReg]
  have h : writeReg β rY (fun _ ↦ (0 : ZMod 2)) = β := by
    rw [show (fun _ : Fin w ↦ (0 : ZMod 2)) = fun i ↦ β (rY i) from
      funext fun i ↦ (hclean i).symm]
    exact writeReg_self β rY
  rw [h]

/-- Disjointness of slices of disjoint registers. -/
theorem disj_slice {N M : ℕ} (rData : QRegister N n) (rAnc : QRegister M n)
    (h : rData.DisjointWires rAnc) (a b : ℕ) (ha : a + b ≤ N) (a' b' : ℕ) (ha' : a' + b' ≤ M) :
    (rData.slice a b ha).DisjointWires (rAnc.slice a' b' ha') :=
  (h.compose_left _).compose_right _

/-- The three phases of the controlled adder on `K + 1` bits: compute `c * x` into the clean
register `rY`, add `rY` into `rB` by the ripple-carry adder, and uncompute `rY`. -/
theorem runList_controlledCore (K : ℕ) (c ci : Wire n) (rX rB rY : QRegister (K + 1) n)
    (rC : QRegister K n) (hXB : rX.DisjointWires rB) (hXY : rX.DisjointWires rY)
    (hBY : rB.DisjointWires rY) (hBC : rB.DisjointWires rC) (hYC : rY.DisjointWires rC)
    (hcX : c ∉ Set.range rX.wires) (hcB : c ∉ Set.range rB.wires) (hcY : c ∉ Set.range rY.wires)
    (hciY : ci ∉ Set.range rY.wires) (hciB : ci ∉ Set.range rB.wires)
    (hciC : ci ∉ Set.range rC.wires)
    (β : BitAssignment n) (hcleanY : ∀ i, β (rY i) = 0) (hcleanC : ∀ i, β (rC i) = 0) :
    runList (andSteps c (K + 1) rX rY ++ rippleSteps K rY rB ci rC ++ unandSteps c (K + 1) rX rY)
        β =
      some (writeReg β rB (basisBits (K + 1) ⟨((if (β c).val = 1 then (localIdx rX β : ℕ) else 0) +
        (localIdx rB β : ℕ) + (β ci).val) % 2 ^ (K + 1), Nat.mod_lt _ (by positivity)⟩)) := by
  obtain ⟨g, hg⟩ : ∃ g : BitAssignment (K + 1), g = basisBits (K + 1)
      ⟨((if (β c).val = 1 then (localIdx rX β : ℕ) else 0) + (localIdx rB β : ℕ) + (β ci).val) %
        2 ^ (K + 1), Nat.mod_lt _ (by positivity)⟩ := ⟨_, rfl⟩
  rw [← hg]
  have hYB := QRegister.disjoint_comm.mp hBY
  have hCY := QRegister.disjoint_comm.mp hYC
  have h1 := runList_andSteps c (K + 1) rX rY hXY hcX hcY β hcleanY
  have hcl1 : ∀ i, writeReg β rY (fun i ↦ β c * β (rX i)) (rC i) = 0 := fun i ↦ by
    rw [writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hCY i)]
    exact hcleanC i
  have hrip := runList_rippleSteps K rY rB ci rC hYB hYC hBC hciY hciB hciC
    (writeReg β rY (fun i ↦ β c * β (rX i))) hcl1
  have hrip' : runList (rippleSteps K rY rB ci rC) (writeReg β rY (fun i ↦ β c * β (rX i))) =
      some (writeReg (writeReg β rY (fun i ↦ β c * β (rX i))) rB g) := by
    rw [hrip, hg]
    refine congrArg some (congrArg (writeReg _ rB) (congrArg (basisBits (K + 1)) (Fin.ext ?_)))
    dsimp only
    rw [localIdx_andSteps, localIdx_writeReg_of_disjoint _ _ _ hYB,
      writeReg_apply_of_not_mem _ _ _ _ hciY]
  have hv : ∀ i, (writeReg (writeReg β rY (fun i ↦ β c * β (rX i))) rB g) (rY i) =
      (writeReg (writeReg β rY (fun i ↦ β c * β (rX i))) rB g) c *
        (writeReg (writeReg β rY (fun i ↦ β c * β (rX i))) rB g) (rX i) := fun i ↦ by
    rw [writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hYB i),
      writeReg_apply_of_not_mem _ _ _ _ hcB,
      writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hXB i), writeReg_apply_reg,
      writeReg_apply_of_not_mem _ _ _ _ hcY,
      writeReg_apply_of_not_mem _ _ _ _ (not_mem_of_disjoint hXY i)]
  rw [runList_append, runList_append, h1, Option.bind_some, hrip', Option.bind_some,
    runList_unandSteps c (K + 1) rX rY hXY hcX hcY _ hv]
  exact congrArg some (writeReg_chain β rY rB hBY _ g hcleanY)

/-- The number read from the data register: target, then addend, then the control bit. -/
theorem localIdx_data (k : ℕ) (rData : QRegister (1 + k + k) n) (β : BitAssignment n) :
    (localIdx rData β : ℕ) = (localIdx (rData.slice 0 k (by omega)) β : ℕ) +
      2 ^ k * ((localIdx (rData.slice k k (by omega)) β : ℕ) +
        2 ^ k * (β (rData ⟨2 * k, by omega⟩)).val) := by
  have hc : (localIdx ((rData.slice k (k + 1) (by omega)).slice k 1 (by omega)) β : ℕ) =
      (β (rData ⟨2 * k, by omega⟩)).val := by
    rw [localIdx_val, Fin.sum_univ_one]
    have e : (rData.slice k (k + 1) (by omega)).slice k 1 (by omega) 0 =
        rData ⟨2 * k, by omega⟩ := by
      rw [QRegister.slice_apply, QRegister.slice_apply]
      congr 1
      ext
      simp only [Fin.val_zero]
      omega
    rw [e]
    simp
  rw [localIdx_val_split rData k (k + 1) (by omega),
    localIdx_val_split (rData.slice k (k + 1) (by omega)) k 1 (by omega), hc]
  simp only [localIdx_slice_slice, add_zero]

/-- Step list of the controlled adder on `k` bits. -/
def controlledAdderSteps : (k : ℕ) → QRegister (1 + k + k) n → QRegister (2 * k) n →
    List (Step n)
  | 0, _, _ => []
  | K + 1, rData, rAnc =>
      andSteps (rData ⟨2 * (K + 1), by omega⟩) (K + 1) (rData.slice (K + 1) (K + 1) (by omega))
        (rAnc.slice 0 (K + 1) (by omega)) ++
      rippleSteps K (rAnc.slice 0 (K + 1) (by omega)) (rData.slice 0 (K + 1) (by omega))
        (rAnc ⟨K + 1, by omega⟩) (rAnc.slice (K + 2) K (by omega)) ++
      unandSteps (rData ⟨2 * (K + 1), by omega⟩) (K + 1) (rData.slice (K + 1) (K + 1) (by omega))
        (rAnc.slice 0 (K + 1) (by omega))

theorem andCount_controlledAdderSteps (k : ℕ) (rData : QRegister (1 + k + k) n)
    (rAnc : QRegister (2 * k) n) :
    ((controlledAdderSteps k rData rAnc).map Step.andCount).sum = k + (k - 1) := by
  cases k with
  | zero => rfl
  | succ K =>
    rw [controlledAdderSteps, List.map_append, List.map_append, List.sum_append, List.sum_append,
      andCount_andSteps, andCount_unandSteps, andCount_rippleSteps]
    omega

theorem runList_controlledAdderSteps (k : ℕ) (rData : QRegister (1 + k + k) n)
    (rAnc : QRegister (2 * k) n) (hdisj : rData.DisjointWires rAnc)
    (σ : Equiv.Perm (Fin (2 ^ (1 + k + k))))
    (hσ : ∀ j : Fin (2 ^ (1 + k + k)), (σ j : ℕ) =
      ((j : ℕ) % 2 ^ k + (if (j : ℕ) / 2 ^ k / 2 ^ k = 1 then (j : ℕ) / 2 ^ k % 2 ^ k else 0)) %
        2 ^ k + 2 ^ k * ((j : ℕ) / 2 ^ k))
    (β : BitAssignment n) (hβ : localIdx rAnc β = 0) :
    runList (controlledAdderSteps k rData rAnc) β =
      some (writeReg β rData (basisBits (1 + k + k) (σ (localIdx rData β)))) := by
  cases k with
  | zero =>
    have h : σ (localIdx rData β) = localIdx rData β := Fin.ext (by
      rw [hσ]
      simp only [pow_zero, Nat.div_one, one_mul]
      split_ifs <;> omega)
    rw [controlledAdderSteps, runList_nil, h, basisBits_basisBitsEquiv_symm, writeReg_self]
  | succ K =>
    have hclean := eq_zero_of_localIdx_eq_zero rAnc β hβ
    have hci : β (rAnc ⟨K + 1, by omega⟩) = 0 := hclean _
    have hBX : (rData.slice 0 (K + 1) (by omega)).DisjointWires
        (rData.slice (K + 1) (K + 1) (by omega)) :=
      QRegister.slice_disjoint_of_le rData 0 (K + 1) (K + 1) (K + 1) (by omega) (by omega)
        (by omega)
    have hYC : (rAnc.slice 0 (K + 1) (by omega)).DisjointWires (rAnc.slice (K + 2) K (by omega)) :=
      QRegister.slice_disjoint_of_le rAnc 0 (K + 1) (K + 2) K (by omega) (by omega) (by omega)
    have hcB : rData ⟨2 * (K + 1), by omega⟩ ∉ Set.range (rData.slice 0 (K + 1) (by omega)).wires :=
      apply_not_mem_slice rData _ 0 (K + 1) (by omega) (Or.inr (by dsimp; omega))
    have key := runList_controlledCore K (rData ⟨2 * (K + 1), by omega⟩) (rAnc ⟨K + 1, by omega⟩)
      (rData.slice (K + 1) (K + 1) (by omega)) (rData.slice 0 (K + 1) (by omega))
      (rAnc.slice 0 (K + 1) (by omega)) (rAnc.slice (K + 2) K (by omega))
      (QRegister.disjoint_comm.mp hBX)
      (disj_slice rData rAnc hdisj _ _ _ _ _ _)
      (disj_slice rData rAnc hdisj _ _ _ _ _ _)
      (disj_slice rData rAnc hdisj _ _ _ _ _ _)
      hYC
      (apply_not_mem_slice rData _ (K + 1) (K + 1) (by omega) (Or.inr (by dsimp; omega)))
      hcB
      (fun ⟨i, h⟩ ↦ hdisj.ne _ _ h.symm)
      (apply_not_mem_slice rAnc _ 0 (K + 1) (by omega) (Or.inr (by dsimp; omega)))
      (fun ⟨i, h⟩ ↦ hdisj.ne _ _ h)
      (apply_not_mem_slice rAnc _ (K + 2) K (by omega) (Or.inl (by dsimp; omega)))
      β (fun _ ↦ hclean _) (fun _ ↦ hclean _)
    rw [controlledAdderSteps, key]
    refine congrArg some ?_
    rw [← writeReg_eq_of_eqOn β (writeReg β (rData.slice 0 (K + 1) (by omega)) _) rData
      fun w hw ↦ writeReg_apply_of_not_mem _ _ _ _ fun ⟨i, h⟩ ↦ hw ⟨_, h⟩]
    congr 1
    rw [← basisBits_basisBitsEquiv_symm (1 + (K + 1) + (K + 1)) (fun p ↦ _)]
    congr 1
    apply Fin.ext
    have hL : ∀ γ : BitAssignment n,
        ((basisBits (1 + (K + 1) + (K + 1))).symm (fun p ↦ γ (rData p)) : Fin _) =
          localIdx rData γ := fun _ ↦ rfl
    rw [hL, hσ, localIdx_data (K + 1) rData (writeReg β _ _), localIdx_data (K + 1) rData β,
      localIdx_writeReg, basisBitsEquiv_symm_basisBits,
      localIdx_writeReg_of_disjoint _ _ _ hBX, writeReg_apply_of_not_mem _ _ _ _ hcB, hci]
    simp only [ZMod.val_zero]
    exact (controlled_arith (K + 1) _ _ _ (localIdx (rData.slice 0 (K + 1) (by omega)) β).isLt
      (localIdx (rData.slice (K + 1) (K + 1) (by omega)) β).isLt).symm

end ControlledAdderImpl

open ArcsinImpl ArcsinImpl.Step

/-- Number of clean ancilla qubits `controlledAdderProgram` uses at bit-width `k`. -/
def controlledAdderAncillas (k : ℕ) : ℕ := 2 * k

/-- Parameterized controlled adder on `1 + k + k` data wires `rData` (`k` target wires `b`, followed
by `k` addend wires `x`, each least-significant bit first, and then the control wire `c`) and
`controlledAdderAncillas k` clean ancilla wires `rAnc`. -/
def controlledAdderProgram {n : ℕ} (k : ℕ)
    (rData : QRegister (1 + k + k) n)
    (rAnc : QRegister (controlledAdderAncillas k) n) : DynamicCircuit Var n :=
  compileList v (ControlledAdderImpl.controlledAdderSteps k rData rAnc)

/-- Parameterized correctness theorem: for every bit-width `k`, `controlledAdderProgram k` realizes
`controlledAdderUnitary k` as an exact clean subroutine across all disjoint register placements. -/
theorem controlled_adder_correctness (k : ℕ) :
    ∀ {n : ℕ}
      (rData : QRegister (1 + k + k) n)
      (rAnc : QRegister (controlledAdderAncillas k) n)
      (hdisj : rData.DisjointWires rAnc),
      RealizesCleanSubroutine rData rAnc hdisj (controlledAdderUnitary k)
        (controlledAdderProgram k rData rAnc).compile := by
  intro n rData rAnc hdisj
  refine realizesCleanSubroutine_compileList v _ rData rAnc hdisj
    (tableAddPerm (controlledAddend k)) fun β hβ ↦ ?_
  exact ControlledAdderImpl.runList_controlledAdderSteps k rData rAnc hdisj _
    (fun j ↦ ControlledAdderImpl.controlledAddPerm_val k j) β hβ

/-- `T`-gate count of `controlledAdderProgram k`, which the cost predicates require to use no `TOFF`
gates. -/
abbrev controlledAdderTCount {n : ℕ} (k : ℕ)
    (rData : QRegister (1 + k + k) n)
    (rAnc : QRegister (controlledAdderAncillas k) n) : ℕ :=
  (controlledAdderProgram k rData rAnc).count PrimitiveGate.T

/-- Spacetime cost `T count * qubits` of `controlledAdderProgram k`, counting all
`1 + k + k + controlledAdderAncillas k` data and clean ancilla qubits. -/
abbrev controlledAdderSpacetime {n : ℕ} (k : ℕ)
    (rData : QRegister (1 + k + k) n)
    (rAnc : QRegister (controlledAdderAncillas k) n) : ℕ :=
  controlledAdderTCount k rData rAnc * (1 + k + k + controlledAdderAncillas k)

/-!
## Cost Predicates

Both predicates forbid primitive `TOFF` gates (so every Toffoli must be decomposed into Clifford +
`T` + measurements) and bound a cost of `controlledAdderProgram` at bit-width `k` across all
register placements.
-/

/-- `controlledAdderProgram` at bit-width `k` uses no primitive `TOFF` gates and has `T` count at
most `cost`, across all register placements. -/
abbrev SatisfiesControlledAdderTBound (k cost : ℕ) : Prop :=
  ∀ {n : ℕ}
    (rData : QRegister (1 + k + k) n)
    (rAnc : QRegister (controlledAdderAncillas k) n),
    (controlledAdderProgram k rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      controlledAdderTCount k rData rAnc ≤ cost

/-- `controlledAdderProgram` at bit-width `k` uses no primitive `TOFF` gates and has spacetime cost
at most `cost`, for every constant and register placement it can be given. -/
abbrev SatisfiesControlledAdderSpacetimeBound (k cost : ℕ) : Prop :=
  ∀ {n : ℕ}
    (rData : QRegister (1 + k + k) n)
    (rAnc : QRegister (controlledAdderAncillas k) n),
    (controlledAdderProgram k rData rAnc).count PrimitiveGate.TOFF = 0 ∧
      controlledAdderSpacetime k rData rAnc ≤ cost

/-- The baseline uses no `TOFF` gates and at most `4 * k + 4 * (k - 1)` `T` gates. -/
theorem controlled_adder_baseline_t_bound (k : ℕ) :
    SatisfiesControlledAdderTBound k (4 * k + 4 * (k - 1)) := by
  intro n rData rAnc
  refine ⟨count_TOFF_compileList v _, ?_⟩
  have h := count_T_compileList v (ControlledAdderImpl.controlledAdderSteps k rData rAnc)
  have h2 := ControlledAdderImpl.andCount_controlledAdderSteps k rData rAnc
  refine le_trans h ?_
  omega

/-- The baseline has spacetime cost at most `(4 * k + 4 * (k - 1)) * (1 + k + k + 2 * k)`. -/
theorem controlled_adder_baseline_spacetime_bound (k : ℕ) :
    SatisfiesControlledAdderSpacetimeBound k ((4 * k + 4 * (k - 1)) * (1 + k + k + 2 * k)) := by
  intro n rData rAnc
  exact ⟨(controlled_adder_baseline_t_bound k rData rAnc).1,
    Nat.mul_le_mul_right _ (controlled_adder_baseline_t_bound k rData rAnc).2⟩

/-!
## Cost Theorems at Every Bit-Width
-/

/-- Claimed `T` count of `controlledAdderProgram`, as a function of the bit-width `k`. -/
def controlledAdderTCost (k : ℕ) : ℕ := 4 * k + 4 * (k - 1)

theorem controlled_adder_t_cost (k : ℕ) :
    SatisfiesControlledAdderTBound k (controlledAdderTCost k) :=
  controlled_adder_baseline_t_bound k

/-- Claimed spacetime cost of `controlledAdderProgram`, as a function of the bit-width `k`. -/
def controlledAdderSpacetimeCost (k : ℕ) : ℕ := (4 * k + 4 * (k - 1)) * (1 + k + k + 2 * k)

theorem controlled_adder_spacetime_cost (k : ℕ) :
    SatisfiesControlledAdderSpacetimeBound k (controlledAdderSpacetimeCost k) :=
  controlled_adder_baseline_spacetime_bound k

/-!
## Cost Theorems at the Pinned Bit-Widths `k = 64` and `k = 2048`
-/

/-- Claimed `T` count bound for `controlledAdderProgram` at `k = 64`. -/
def controlledAdderK64TCost : ℕ := 508

theorem controlled_adder_k64_t_cost :
    SatisfiesControlledAdderTBound 64 controlledAdderK64TCost :=
  controlled_adder_baseline_t_bound 64

/-- Claimed spacetime cost bound for `controlledAdderProgram` at `k = 64`. -/
def controlledAdderK64SpacetimeCost : ℕ := 130556

theorem controlled_adder_k64_spacetime_cost :
    SatisfiesControlledAdderSpacetimeBound 64 controlledAdderK64SpacetimeCost :=
  controlled_adder_baseline_spacetime_bound 64

/-- Claimed `T` count bound for `controlledAdderProgram` at `k = 2048`. -/
def controlledAdderK2048TCost : ℕ := 16380

theorem controlled_adder_k2048_t_cost :
    SatisfiesControlledAdderTBound 2048 controlledAdderK2048TCost :=
  controlled_adder_baseline_t_bound 2048

/-- Claimed spacetime cost bound for `controlledAdderProgram` at `k = 2048`. -/
def controlledAdderK2048SpacetimeCost : ℕ := 134201340

theorem controlled_adder_k2048_spacetime_cost :
    SatisfiesControlledAdderSpacetimeBound 2048 controlledAdderK2048SpacetimeCost :=
  controlled_adder_baseline_spacetime_bound 2048

end QuantumComputation.Specs
