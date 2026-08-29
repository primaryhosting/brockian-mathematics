import Mathlib
/-!
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix

/-- The primitive `8`-th root of unity `ω = exp(2πi/8)` used by the 3-qubit QFT. -/

noncomputable def qftOmega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)

/-- The 3-qubit quantum Fourier transform matrix: the `8 × 8` matrix with entries
`(1/√8) · ω^(jk)`, where `ω = exp(2πi/8)`. -/
