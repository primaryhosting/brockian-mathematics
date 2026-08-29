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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

/-- The Toffoli (CCNOT) gate as an `8 × 8` complex matrix, acting on the computational
basis `|abc⟩` ordered as `000, 001, 010, 011, 100, 101, 110, 111`.  It is the identity
except that it exchanges the last two basis vectors `|110⟩` and `|111⟩`. -/
def toffoli : Matrix (Fin 8) (Fin 8) ℂ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0, 1, 0]

/-- The underlying permutation of basis states: the transposition of `|110⟩` and `|111⟩`. -/
def toffoliPerm : Equiv.Perm (Fin 8) := Equiv.swap 6 7

/-- The Toffoli matrix is the permutation matrix of the transposition `(6 7)`. -/
theorem toffoli_eq_permMatrix : toffoli = toffoliPerm.permMatrix ℂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toffoli, toffoliPerm, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.swap_apply_def, Fin.ext_iff]

/-- The Toffoli matrix is real symmetric, so its conjugate transpose is itself. -/
theorem toffoli_conjTranspose : toffoliᴴ = toffoli := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toffoli, Matrix.conjTranspose_apply]

/-- The Toffoli gate is its own inverse. -/
theorem toffoli_mul_self : toffoli * toffoli = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toffoli, Matrix.mul_apply, Fin.sum_univ_succ]

/-- **Toffoli is a unitary involution.**
The Toffoli (CCNOT) matrix is the permutation matrix of the transposition `(|110⟩ |111⟩)`;
consequently it lies in the unitary group, satisfies `Uᴴ * U = U * Uᴴ = 1`, and is its
own inverse (`U * U = 1`, `U⁻¹ = U`). -/
theorem toffoli_unitary :
    toffoli = toffoliPerm.permMatrix ℂ ∧
    toffoli ∈ Matrix.unitaryGroup (Fin 8) ℂ ∧
    toffoliᴴ * toffoli = 1 ∧
    toffoli * toffoliᴴ = 1 ∧
    toffoli * toffoli = 1 ∧
    toffoli⁻¹ = toffoli := by
  have hH : toffoliᴴ = toffoli := toffoli_conjTranspose
  have hmul : toffoli * toffoli = 1 := toffoli_mul_self
  refine ⟨toffoli_eq_permMatrix, ?_, ?_, ?_, hmul, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    simpa [Matrix.star_eq_conjTranspose, hH] using hmul
  · rw [hH]; exact hmul
  · rw [hH]; exact hmul
  · exact Matrix.inv_eq_right_inv hmul

end QC

