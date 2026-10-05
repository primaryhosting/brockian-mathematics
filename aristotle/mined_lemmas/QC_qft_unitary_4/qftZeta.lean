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

noncomputable def qftZeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 16)

/-- The `16 × 16` matrix of the quantum Fourier transform on 4 qubits:
`Q j k = (1/4) * exp (2πi j k / 16)`. -/
