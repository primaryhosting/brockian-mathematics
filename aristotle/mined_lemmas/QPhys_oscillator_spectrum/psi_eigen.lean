/-!
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial

namespace QPhys

/-! ## Hermite polynomials over `ℝ`

We reuse Mathlib's (probabilists') Hermite polynomials `Polynomial.hermite : ℕ → ℤ[X]`
(`Mathlib/RingTheory/Polynomial/Hermite/Basic.lean`), pushed forward to `ℝ[X]`.
-/

/-- The `n`-th (probabilists') Hermite polynomial, with real coefficients. -/

lemma psi_eigen (n : ℕ) (y : ℝ) :
    -deriv (deriv (psi n)) y + (y ^ 2 / 4) * psi n y = ((n : ℝ) + 1 / 2) * psi n y := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval y) (Dop_Dop_Hr n)
  simp only [eval_add, eval_mul, eval_neg, eval_C, eval_pow, eval_X, eval_natCast] at h
  rw [deriv_deriv_psi n]
  simp only [psi]
  nlinarith [h, Real.exp_pos (-(y ^ 2 / 4))]

