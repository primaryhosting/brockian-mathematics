/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex Matrix Finset

/-- The primitive `N`-th root of unity `exp (2πi / N)` used in the QFT. -/

noncomputable def qftRoot (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- The `N`-point discrete Fourier transform (quantum Fourier transform) matrix:
`(QFT_N) j k = N^(-1/2) * exp (2πi j k / N)`. -/
