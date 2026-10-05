/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex Matrix Finset

/-- The primitive `64`-th root of unity `exp (2πi/64)` used by the 6-qubit QFT. -/

noncomputable def qftOmega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 64)

/-- The 6-qubit quantum Fourier transform matrix, of size `2^6 = 64`:
its `(j,k)` entry is `ω^(j*k) / √64 = ω^(j*k) / 8` with `ω = exp (2πi/64)`. -/
