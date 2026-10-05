/-
# Cnot Unitary Involutive
Category: Quantum Computing
Target: QC.cnot_unitary_involutive
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

/-- The controlled-NOT gate, as a `4 × 4` complex matrix acting on two qubits
(basis ordered `|00⟩, |01⟩, |10⟩, |11⟩`): it flips the target qubit exactly when
the control qubit is `1`. -/
def cnot : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

/-- `CNOT` is its own conjugate transpose (it is real and symmetric). -/
theorem cnot_conjTranspose : cnotᴴ = cnot := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cnot, Matrix.conjTranspose_apply]

/-- `CNOT` squares to the identity. -/
theorem cnot_mul_self : cnot * cnot = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cnot, Matrix.mul_apply, Fin.sum_univ_succ]

/-- **CNOT is unitary and involutive**: `CNOTᴴ * CNOT = CNOT * CNOTᴴ = I`
(equivalently `CNOT ∈ unitary`), and `CNOT ^ 2 = I`. -/
theorem cnot_unitary_involutive :
    cnot ∈ unitary (Matrix (Fin 4) (Fin 4) ℂ) ∧ cnot * cnot = 1 ∧ cnot ^ 2 = 1 := by
  have hsq : cnot * cnot = 1 := cnot_mul_self
  refine ⟨?_, hsq, ?_⟩
  · constructor
    · simpa [Matrix.star_eq_conjTranspose, cnot_conjTranspose] using hsq
    · simpa [Matrix.star_eq_conjTranspose, cnot_conjTranspose] using hsq
  · rw [pow_two, hsq]

end QC

