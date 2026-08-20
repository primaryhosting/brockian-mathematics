/-
# Toffoli Unitary
Category: Quantum Computing
Target: QC.toffoli_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

open Matrix

/-- The Toffoli (CCNOT) gate as an explicit `8 × 8` complex matrix, in the standard
computational-basis ordering `|000⟩, |001⟩, …, |111⟩`: it is the identity except that the
last two basis states `|110⟩` and `|111⟩` are exchanged. -/
noncomputable def toffoli : Matrix (Fin 8) (Fin 8) ℂ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0, 1, 0]

/-- The underlying permutation of basis states: the transposition `|110⟩ ↔ |111⟩`. -/
def toffoliPerm : Equiv.Perm (Fin 8) := Equiv.swap 6 7

/-- Encoding of a three-bit string `(a, b, c)` as an index in `Fin 8`, with `a` the most
significant bit. -/
def idx (a b c : Bool) : Fin 8 :=
  ⟨4 * a.toNat + 2 * b.toNat + c.toNat, by cases a <;> cases b <;> cases c <;> decide⟩

/-- The Toffoli permutation flips the target bit `c` exactly when both control bits are set. -/
theorem toffoliPerm_idx (a b c : Bool) :
    toffoliPerm (idx a b c) = idx a b (xor c (a && b)) := by
  cases a <;> cases b <;> cases c <;> decide

/-- `toffoli` is the permutation matrix of `toffoliPerm`. -/
theorem toffoli_eq_permMatrix : toffoli = toffoliPerm.permMatrix ℂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toffoli, toffoliPerm, Equiv.Perm.permMatrix, Equiv.swap_apply_def]

/-- `toffoli` is self-adjoint (it is a real symmetric permutation matrix). -/
theorem toffoli_conjTranspose : toffoliᴴ = toffoli := by
  rw [toffoli_eq_permMatrix, Matrix.conjTranspose_permMatrix]
  simp [toffoliPerm]

/-- Action on computational basis states: `|a, b, c⟩ ↦ |a, b, c ⊕ (a ∧ b)⟩`. -/
theorem toffoli_mulVec_basis (a b c : Bool) :
    toffoli *ᵥ (Pi.single (idx a b c) (1 : ℂ)) =
      Pi.single (idx a b (xor c (a && b))) (1 : ℂ) := by
  rw [toffoli_eq_permMatrix, Matrix.permMatrix_mulVec]
  funext i
  cases a <;> cases b <;> cases c <;>
    fin_cases i <;>
      simp [toffoliPerm, idx, Pi.single_apply, Equiv.swap_apply_def, Fin.ext_iff]

/-- **The Toffoli matrix is a permutation matrix, hence unitary, and is its own inverse.**
It satisfies `toffoliᴴ * toffoli = 1`, `toffoli * toffoliᴴ = 1`, it lies in the unitary group,
and `toffoli * toffoli = 1`. -/
theorem toffoli_unitary :
    toffoliᴴ * toffoli = 1 ∧ toffoli * toffoliᴴ = 1 ∧
      toffoli ∈ Matrix.unitaryGroup (Fin 8) ℂ ∧ toffoli * toffoli = 1 := by
  have hsq : toffoli * toffoli = 1 := by
    rw [toffoli_eq_permMatrix, ← Matrix.permMatrix_mul]
    have : toffoliPerm * toffoliPerm = 1 := by
      simp [toffoliPerm, Equiv.swap_mul_self]
    rw [this, Matrix.permMatrix_one]
  have h1 : toffoliᴴ * toffoli = 1 := by rw [toffoli_conjTranspose]; exact hsq
  have h2 : toffoli * toffoliᴴ = 1 := by rw [toffoli_conjTranspose]; exact hsq
  exact ⟨h1, h2, Matrix.mem_unitaryGroup_iff.mpr h2, hsq⟩

end QC

