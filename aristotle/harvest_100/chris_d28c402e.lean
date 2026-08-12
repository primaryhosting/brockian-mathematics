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

/-- The CNOT gate as a `4 × 4` complex matrix, in the computational basis
ordering `|00⟩, |01⟩, |10⟩, |11⟩`: it flips the target qubit exactly when the
control qubit is `1`. -/
def cnot : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

theorem cnot_conjTranspose : cnot.conjTranspose = cnot := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cnot, Matrix.conjTranspose_apply]

theorem cnot_mul_self : cnot * cnot = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cnot, Matrix.mul_apply, Fin.sum_univ_four]

/-- CNOT is unitary and squares to the identity. -/
theorem cnot_unitary_involutive :
    cnot ∈ unitary (Matrix (Fin 4) (Fin 4) ℂ) ∧ cnot * cnot = 1 := by
  refine ⟨?_, cnot_mul_self⟩
  constructor
  · show cnot.conjTranspose * cnot = 1
    rw [cnot_conjTranspose, cnot_mul_self]
  · show cnot * cnot.conjTranspose = 1
    rw [cnot_conjTranspose, cnot_mul_self]

end QC

