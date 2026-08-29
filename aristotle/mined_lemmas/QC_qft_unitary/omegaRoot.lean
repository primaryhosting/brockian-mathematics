import Mathlib

/-!
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Finset Matrix

/-- The primitive `N`-th root of unity `exp(2πi/N)`. -/

noncomputable def omegaRoot (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- The `N × N` discrete Fourier transform matrix, with entries
`(1/√N) * exp(2πi·jk/N)`. -/
