/-
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above uses a plain block comment because Lean requires `import`
-- to precede any module docstring; the docstring form is repeated below.)

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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

/-- The primitive `N`-th root of unity `exp (2 π i / N)` used by the quantum Fourier
transform on `N` basis states. -/

noncomputable def qftZeta (N : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))

/-- The `N`-dimensional quantum Fourier transform matrix:
`F j k = N^(-1/2) * exp (2 π i j k / N)`. -/

lemma qftZeta_ne_zero (N : ℕ) : qftZeta N ≠ 0 := Complex.exp_ne_zero _
