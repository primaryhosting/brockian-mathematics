import Mathlib

/-!
# Cnot Unitary Involutive
Category: Quantum Computing
Target: QC.cnot_unitary_involutive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace QC

/-- The CNOT gate on two qubits, as a `4 × 4` complex matrix in the
computational basis `|00⟩, |01⟩, |10⟩, |11⟩`. -/
def cnot : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

/-- CNOT is self-adjoint: its conjugate transpose is itself. -/
theorem cnot_conjTranspose : cnot.conjTranspose = cnot := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cnot, Matrix.conjTranspose]

/-- CNOT squares to the identity. -/
theorem cnot_mul_self : cnot * cnot = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cnot, Matrix.mul_apply, Fin.sum_univ_four]

/-- CNOT is unitary (`Uᴴ * U = 1` and `U * Uᴴ = 1`) and involutive (`U * U = 1`). -/
theorem cnot_unitary_involutive :
    cnot.conjTranspose * cnot = 1 ∧ cnot * cnot.conjTranspose = 1 ∧
      cnot * cnot = 1 := by
  refine ⟨?_, ?_, cnot_mul_self⟩ <;> rw [cnot_conjTranspose] <;> exact cnot_mul_self

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

