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

private lemma two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
  simp [Complex.I_ne_zero, Real.pi_ne_zero]

/-- The sum of the 64-th roots of unity `exp(2πi d/64)^k`, `k < 64`. -/
