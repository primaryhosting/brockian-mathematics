import Mathlib

/-!
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
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

set_option grind.warning false

namespace QC

/-- `omega` is the primitive 8th root of unity `exp (2πi/8)` used by the 3-qubit QFT. -/

noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / (8 : ℕ))

/-- The 3-qubit quantum Fourier transform matrix: an `8 × 8` complex matrix with
entries `(1/√8) * ω^(j*k)`, where `ω = exp (2πi/8)`. -/
