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

lemma Dop_Dop_Hr (n : ℕ) :
    -Dop (Dop (Hr n)) + C (1 / 4) * X ^ 2 * Hr n = ((n : Polynomial ℝ) + C (1 / 2)) * Hr n := by
  simp only [Dop, derivative_sub, derivative_mul, derivative_X, derivative_C, mul_one,
    zero_mul, zero_add]
  rw [Hr_ode n]
  apply Polynomial.funext
  intro y
  simp only [eval_add, eval_sub, eval_mul, eval_neg, eval_X, eval_C, eval_pow, eval_natCast]
  ring

/-- Dimensionless eigenvalue equation: `-ψₙ'' + (y²/4) ψₙ = (n + 1/2) ψₙ`. -/
