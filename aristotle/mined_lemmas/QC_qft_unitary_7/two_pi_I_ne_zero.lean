import Mathlib

/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Finset Matrix

/-- The `n × n` quantum Fourier transform matrix, with entries
`exp (2 π i j k / n) / √n`. -/

lemma two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero

/-- Orthogonality of characters: the sum of `exp (2 π i k m / n)` over `k < n`
is `n` if `n ∣ m`, and `0` otherwise. -/
