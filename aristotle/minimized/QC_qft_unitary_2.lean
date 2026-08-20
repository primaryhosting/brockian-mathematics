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

noncomputable def qftMatrix2 : Matrix (Fin 4) (Fin 4) ℂ :=
  fun j k => (1 / 2 : ℂ) * Complex.I ^ ((j.val * k.val) % 4)

/-- The 2-qubit QFT matrix is unitary. -/
