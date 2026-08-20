import Mathlib

/-!
# Qft Unitary 2
Category: Quantum Computing
Target: QC.qft_unitary_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix Complex

/-- The 2-qubit quantum Fourier transform matrix, a `4 × 4` complex matrix whose
`(j, k)` entry is `(1/√4) * ω ^ (j * k)` with `ω = exp(2πi/4) = i`.  Since `i` has
order `4`, the exponent may be reduced modulo `4`. -/

theorem qft_conjTranspose_mul_self_2 : qftMatrix2ᴴ * qftMatrix2 = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp qft_unitary_2

/-- Explicit form of unitarity: `qftMatrix2 * qftMatrix2ᴴ = 1`. -/
