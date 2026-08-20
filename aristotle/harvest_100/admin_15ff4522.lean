/-
# Cnot Unitary Involutive
Category: Quantum Computing
Target: QC.cnot_unitary_involutive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cnot Unitary Involutive
Category: Quantum Computing
Target: QC.cnot_unitary_involutive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace QC

open Matrix

/-- The CNOT gate on two qubits, in the computational basis
`|00⟩, |01⟩, |10⟩, |11⟩` (first qubit is the control). -/
def cnot : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

/-- CNOT is self-adjoint. -/
theorem cnot_conjTranspose : cnotᴴ = cnot := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cnot, Matrix.conjTranspose_apply]

/-- CNOT squares to the identity. -/
theorem cnot_mul_self : cnot * cnot = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cnot, Matrix.mul_apply, Fin.sum_univ_four]

/-- **CNOT is unitary and involutive**: `CNOT⁻¹ = CNOTᴴ` in the sense that
`CNOTᴴ * CNOT = CNOT * CNOTᴴ = 1`, and moreover `CNOT ^ 2 = 1`. -/
theorem cnot_unitary_involutive :
    cnot ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
      cnotᴴ * cnot = 1 ∧ cnot * cnotᴴ = 1 ∧ cnot ^ 2 = 1 := by
  have h : cnotᴴ * cnot = 1 := by rw [cnot_conjTranspose, cnot_mul_self]
  have h' : cnot * cnotᴴ = 1 := by rw [cnot_conjTranspose, cnot_mul_self]
  exact ⟨Matrix.mem_unitaryGroup_iff.2 h', h, h', by rw [pow_two, cnot_mul_self]⟩

end QC

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

