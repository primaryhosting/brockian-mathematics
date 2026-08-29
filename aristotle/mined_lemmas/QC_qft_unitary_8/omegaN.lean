import Mathlib
/-!
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace QC

open Complex Matrix Finset

/-- The primitive `N`-th root of unity `exp (2 π i / N)`. -/

noncomputable def omegaN (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- The `N`-dimensional discrete Fourier transform (QFT) matrix:
`(1 / √N) * ω^(j k)` with `ω = exp (2 π i / N)`. -/
