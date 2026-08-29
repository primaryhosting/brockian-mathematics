import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
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

set_option grind.warning false

namespace QC

/-- The primitive `16`-th root of unity `exp (2πi/16)` used to build the 4-qubit QFT. -/

theorem qft_conjTranspose_mul_self_and_self_mul :
    qft4ᴴ * qft4 = 1 ∧ qft4 * qft4ᴴ = 1 := by
  have h := qft_unitary_4
  rw [Matrix.mem_unitaryGroup_iff'] at h
  refine ⟨by simpa [Matrix.star_eq_conjTranspose] using h, ?_⟩
  simpa [Matrix.star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff.mp qft_unitary_4)

end QC

