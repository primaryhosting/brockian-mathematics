import Mathlib

/-!
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Finset Matrix

/-- The primitive `n`-th root of unity `exp(2πi/n)` used in the quantum Fourier transform. -/

noncomputable def qftOmega (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- The `n`-dimensional quantum Fourier transform matrix,
`F j k = ω^(j*k) / √n` with `ω = exp(2πi/n)`. -/
