/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
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

set_option grind.warning false

namespace QC

open Complex

/-- The `2^6 = 64`-dimensional quantum Fourier transform matrix:
`(QFT)_{j,k} = (1/8) * exp(2πi·jk/64)`, where `1/8 = 1/√64`. -/

theorem qft6_conjTranspose_mul_self_and_self_mul :
    Matrix.conjTranspose qft6 * qft6 = 1 ∧ qft6 * Matrix.conjTranspose qft6 = 1 := by
  have h := qft_unitary_6
  exact ⟨Unitary.star_mul_self_of_mem h, Unitary.mul_star_self_of_mem h⟩

end QC

