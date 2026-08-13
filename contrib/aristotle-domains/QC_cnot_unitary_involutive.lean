/-!
# Cnot Unitary Involutive
Category: Quantum Computing
Target: QC.cnot_unitary_involutive
Statement: CNOT is unitary and CNOT²=I.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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

/-- The CNOT gate as a `4 × 4` complex matrix, in the computational basis
`|00⟩, |01⟩, |10⟩, |11⟩`. -/
def CNOT : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

/-- CNOT is unitary (`CNOTᴴ * CNOT = 1` and `CNOT * CNOTᴴ = 1`) and is an
involution (`CNOT * CNOT = 1`). -/
theorem cnot_unitary_involutive :
    QC.CNOT.conjTranspose * QC.CNOT = 1 ∧ QC.CNOT * QC.CNOT.conjTranspose = 1 ∧
      QC.CNOT * QC.CNOT = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [QC.CNOT, Matrix.mul_apply, Fin.sum_univ_succ]

end QC

#print axioms QC.cnot_unitary_involutive

