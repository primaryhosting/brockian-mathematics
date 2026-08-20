/-
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Complex

namespace QC

/-- The primitive `2^7 = 128`-th root of unity `exp (2πi/128)`. -/

lemma qft_norm_sq : ((1 / Real.sqrt 128 : ℝ) : ℂ) * ((1 / Real.sqrt 128 : ℝ) : ℂ)
    = (1 / 128 : ℂ) := by
  rw [← Complex.ofReal_mul,
    show (1 / Real.sqrt 128) * (1 / Real.sqrt 128) = 1 / (Real.sqrt 128 * Real.sqrt 128) by ring,
    Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The 7-qubit quantum Fourier transform matrix is unitary. -/
