import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Toffoli Unitary
Category: Quantum Computing
Target: QC.toffoli_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace QC

open Matrix

/-- The index in `Fin 8` of the three–qubit computational basis state `|a b c⟩`,
using the standard big-endian binary encoding `4a + 2b + c`. -/
def idx (a b c : Bool) : Fin 8 :=
  ⟨4 * a.toNat + 2 * b.toNat + c.toNat, by cases a <;> cases b <;> cases c <;> decide⟩

/-- The permutation of the eight computational basis states implemented by the Toffoli
(CCNOT) gate: it flips the target bit exactly when both control bits are set, i.e. it
exchanges `|110⟩` and `|111⟩`. -/
def toffoliPerm : Equiv.Perm (Fin 8) := Equiv.swap 6 7

/-- The Toffoli permutation acts as `|a b c⟩ ↦ |a b (c ⊕ (a ∧ b))⟩`. -/
theorem toffoliPerm_idx (a b c : Bool) :
    toffoliPerm (idx a b c) = idx a b (xor c (a && b)) := by
  cases a <;> cases b <;> cases c <;> decide

/-- The Toffoli (CCNOT) matrix, as an explicit `8 × 8` complex matrix. -/
def toffoli : Matrix (Fin 8) (Fin 8) ℂ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0, 1, 0]

/-- The Toffoli matrix is the permutation matrix of `toffoliPerm`: its `(i, j)` entry is
`1` when `j = toffoliPerm i` and `0` otherwise. -/
theorem toffoli_apply (i j : Fin 8) :
    toffoli i j = if j = toffoliPerm i then 1 else 0 := by
  have h : ∀ i : Fin 8, toffoliPerm i = if i = 6 then 7 else if i = 7 then 6 else i := by
    decide
  fin_cases i <;> fin_cases j <;>
    simp [toffoli, h, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Every entry of the Toffoli matrix is `0` or `1`, and each row and each column contains
exactly one `1`: it is a permutation matrix. -/
theorem toffoli_isPermMatrix : toffoli = toffoliPerm.permMatrix ℂ := by
  ext i j
  simp [toffoli_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix, Equiv.toPEquiv,
    eq_comm (a := j)]

/-- The Toffoli matrix is symmetric and real, hence self-adjoint. -/
theorem toffoli_conjTranspose : toffoliᴴ = toffoli := by
  ext i j
  have hinv : ∀ x y : Fin 8, (x = toffoliPerm y) ↔ (y = toffoliPerm x) := by decide
  simp only [Matrix.conjTranspose_apply, toffoli_apply]
  by_cases h : i = toffoliPerm j
  · rw [if_pos h, if_pos ((hinv i j).mp h), star_one]
  · rw [if_neg h, if_neg (fun hj => h ((hinv j i).mp hj)), star_zero]

/-- The Toffoli matrix is its own inverse: `T * T = 1`. -/
theorem toffoli_mul_self : toffoli * toffoli = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have key : ∀ k : Fin 8, toffoli i k * toffoli k j
      = if k = toffoliPerm i then (if j = toffoliPerm k then (1 : ℂ) else 0) else 0 := by
    intro k
    rw [toffoli_apply, toffoli_apply]
    split <;> simp_all
  simp only [key, Finset.sum_ite_eq' Finset.univ (toffoliPerm i)]
  have hinv : toffoliPerm (toffoliPerm i) = i := by
    simp [toffoliPerm]
  simp [hinv, Matrix.one_apply, eq_comm (a := j)]

/-- **Toffoli unitary.** The Toffoli (CCNOT) matrix is a permutation matrix; it is
self-adjoint, unitary, and equal to its own inverse. -/
theorem toffoli_unitary :
    toffoli = toffoliPerm.permMatrix ℂ ∧
    toffoliᴴ = toffoli ∧
    toffoliᴴ * toffoli = 1 ∧
    toffoli * toffoliᴴ = 1 ∧
    toffoli ∈ Matrix.unitaryGroup (Fin 8) ℂ ∧
    toffoli * toffoli = 1 ∧
    toffoli⁻¹ = toffoli := by
  have hT := toffoli_conjTranspose
  have hmul := toffoli_mul_self
  refine ⟨toffoli_isPermMatrix, hT, ?_, ?_, ?_, hmul, ?_⟩
  · rw [hT]; exact hmul
  · rw [hT]; exact hmul
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hT]
    exact hmul
  · exact inv_eq_right_inv hmul

end QC

