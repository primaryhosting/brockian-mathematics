import Mathlib

/-!
# Qft Unitary 2
Category: Quantum Computing
Target: QC.qft_unitary_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The primitive 4-th root of unity `exp (2 π i / 4) = i` used by the 2-qubit QFT. -/

theorem qft2_conjTranspose_mul_self :
    Matrix.conjTranspose qft2 * qft2 = 1 ∧ qft2 * Matrix.conjTranspose qft2 = 1 :=
  ⟨Matrix.mem_unitaryGroup_iff'.mp qft_unitary_2,
   Matrix.mem_unitaryGroup_iff.mp qft_unitary_2⟩

#print axioms qft_unitary_2

end QC

