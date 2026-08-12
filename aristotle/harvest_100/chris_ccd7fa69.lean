/-
# Toffoli Unitary
Category: Quantum Computing
Target: QC.toffoli_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Toffoli Unitary
Category: Quantum Computing
Target: QC.toffoli_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Matrix
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

set_option grind.warning false

namespace QC

/-- The permutation of the computational basis `{|abc⟩}` (indexed by `4a + 2b + c`)
implemented by the Toffoli (CCNOT) gate: it exchanges `|110⟩` and `|111⟩` and fixes
all other basis states. -/
def toffoliPerm : Equiv.Perm (Fin 8) := Equiv.swap 6 7

/-- The Toffoli (CCNOT) matrix, written out explicitly in the computational basis
`|000⟩, |001⟩, …, |111⟩`. -/
def toffoli : Matrix (Fin 8) (Fin 8) ℂ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0, 1, 0]

/-- The Toffoli matrix is the permutation matrix of `toffoliPerm`. -/
theorem toffoli_eq_permMatrix :
    toffoli = Equiv.Perm.permMatrix ℂ toffoliPerm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toffoli, toffoliPerm, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.swap_apply_def]

/-- `toffoliPerm` is an involution. -/
theorem toffoliPerm_mul_self : toffoliPerm * toffoliPerm = 1 := by
  simp [toffoliPerm, Equiv.swap_mul_self]

/-- The conjugate transpose of the Toffoli matrix is itself: it is real and symmetric. -/
theorem toffoli_conjTranspose : toffoliᴴ = toffoli := by
  rw [toffoli_eq_permMatrix, Matrix.conjTranspose_permMatrix,
    inv_eq_iff_mul_eq_one.mpr toffoliPerm_mul_self]

/-- The Toffoli matrix is its own inverse. -/
theorem toffoli_mul_self : toffoli * toffoli = 1 := by
  rw [toffoli_eq_permMatrix, ← Matrix.permMatrix_mul, toffoliPerm_mul_self,
    Matrix.permMatrix_one]

/-- **The Toffoli (CCNOT) matrix is unitary.**
It is the permutation matrix of the involutive permutation `toffoliPerm`, hence unitary,
and moreover equal to its own inverse (`toffoli_mul_self`). -/
theorem toffoli_unitary : toffoli ∈ Matrix.unitaryGroup (Fin 8) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, toffoli_conjTranspose,
    toffoli_mul_self]

/-- The inverse of the Toffoli matrix (as a unitary) is the Toffoli matrix itself. -/
theorem toffoli_inv_eq_self :
    (⟨toffoli, toffoli_unitary⟩ : Matrix.unitaryGroup (Fin 8) ℂ)⁻¹
      = ⟨toffoli, toffoli_unitary⟩ := by
  rw [inv_eq_iff_mul_eq_one]
  ext i j
  simpa using congrFun (congrFun toffoli_mul_self i) j

end QC

