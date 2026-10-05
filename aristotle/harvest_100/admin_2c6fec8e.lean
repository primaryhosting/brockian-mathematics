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

/-- The CNOT gate, as a `4 × 4` complex matrix acting on the two-qubit basis
`|00⟩, |01⟩, |10⟩, |11⟩` (control = first qubit). -/
def cnot : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

/-- CNOT is self-adjoint: it equals its own conjugate transpose. -/
theorem cnot_conjTranspose : cnotᴴ = cnot := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cnot, Matrix.conjTranspose]

/-- CNOT is unitary and involutive: `CNOTᴴ * CNOT = 1`, `CNOT * CNOTᴴ = 1`
and `CNOT * CNOT = 1`. -/
theorem cnot_unitary_involutive :
    cnotᴴ * cnot = 1 ∧ cnot * cnotᴴ = 1 ∧ cnot * cnot = 1 := by
  have hsq : cnot * cnot = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cnot, Matrix.mul_apply, Fin.sum_univ_succ]
  refine ⟨?_, ?_, hsq⟩ <;> rw [cnot_conjTranspose] <;> exact hsq

/-- Consequently, CNOT is a member of the unitary group `U(4)`. -/
theorem cnot_mem_unitaryGroup : cnot ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  exact cnot_unitary_involutive.1

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

