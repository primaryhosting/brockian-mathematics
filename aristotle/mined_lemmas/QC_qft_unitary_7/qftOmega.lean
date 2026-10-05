import Mathlib
/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix Finset

/-- The primitive `N`-th root of unity `exp (2πi/N)` used to build the QFT matrix. -/

noncomputable def qftOmega (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- The `N`-point quantum Fourier transform matrix, `F j k = ω^(j*k) / √N`. -/
