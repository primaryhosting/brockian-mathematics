/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex Finset Matrix

/-- The primitive `n`-th root of unity `exp (2 π i / n)` used in the QFT. -/

noncomputable def qftOmega (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- The `n`-dimensional quantum Fourier transform matrix,
`F j k = ω ^ (j * k) / √n` with `ω = exp (2 π i / n)`. -/
