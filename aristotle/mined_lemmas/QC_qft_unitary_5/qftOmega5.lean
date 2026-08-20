/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
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

/-- The primitive `32`-nd root of unity used by the 5-qubit quantum Fourier transform. -/

noncomputable def qftOmega5 : ℂ := Complex.exp (2 * Real.pi * Complex.I / (32 : ℕ))

/-- The 5-qubit quantum Fourier transform matrix, of size `2 ^ 5 = 32`:
`F j k = ω ^ (j * k) / √32` with `ω = exp (2 π i / 32)`. -/
