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

lemma Hr_ode (n : ℕ) :
    derivative (derivative (Hr n)) = X * derivative (Hr n) - (n : Polynomial ℝ) * Hr n := by
  cases n with
  | zero => simp [Hr_zero]
  | succ n =>
      rw [Hr_deriv_succ n]
      simp only [derivative_mul, derivative_add, derivative_natCast, derivative_one, zero_add,
        zero_mul]
      rw [Hr_succ n]
      push_cast
      ring

