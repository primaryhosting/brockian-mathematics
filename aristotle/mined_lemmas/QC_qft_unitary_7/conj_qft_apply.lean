/-
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex Finset

/-- The `n`-qubit quantum Fourier transform matrix, of size `2^n × 2^n`:
`F j k = exp (2πi·jk / 2^n) / √(2^n)`. -/

lemma conj_qft_apply (n : ℕ) (m j : Fin (2 ^ n)) :
    (starRingEnd ℂ) (qft n m j)
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((m : ℕ) * (j : ℕ)) / ((2 : ℂ) ^ n))) /
        ((Real.sqrt (2 ^ n) : ℝ) : ℂ) := by
  simp only [qft, map_div₀, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, map_pow, map_ofNat, Complex.conj_I, Complex.conj_natCast,
    Complex.conj_ofReal]
  ring

/-- A nontrivial geometric sum of `N`-th roots of unity vanishes. -/
