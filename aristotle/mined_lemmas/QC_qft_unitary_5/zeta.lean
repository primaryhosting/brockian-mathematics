/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
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

/-- The `n`-dimensional Quantum Fourier Transform matrix:
`(QFT n) j k = n^(-1/2) * exp (2 π i j k / n)`. -/

noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))

