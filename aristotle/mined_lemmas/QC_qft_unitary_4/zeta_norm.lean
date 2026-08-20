/-
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# The quantum Fourier transform is unitary

We define the `n`-point discrete/quantum Fourier transform matrix

`qftMatrix n = (1/√n) * (ω^(j*k))_{j,k}` with `ω = exp (2πi/n)`,

prove it is unitary for every `n ≠ 0`, and specialize to the 4-qubit case `n = 2^4 = 16`,
giving the target theorem `QC.qft_unitary_4`.
-/

namespace QC

open Complex Matrix Finset

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma zeta_norm (n : ℕ) [NeZero n] : ‖zeta n‖ = 1 := by
  have h : ‖zeta n‖ ^ n = 1 := by rw [← norm_pow, zeta_pow_self n, norm_one]
  rcases lt_trichotomy ‖zeta n‖ 1 with hlt | heq | hgt
  · have := pow_lt_one₀ (norm_nonneg (zeta n)) hlt (NeZero.ne n)
    rw [h] at this
    exact absurd this (lt_irrefl 1)
  · exact heq
  · have := one_lt_pow₀ hgt (NeZero.ne n)
    rw [h] at this
    exact absurd this (lt_irrefl 1)

