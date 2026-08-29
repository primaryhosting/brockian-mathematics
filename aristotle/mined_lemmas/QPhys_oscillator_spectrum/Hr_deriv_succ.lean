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

lemma Hr_deriv_succ (n : ℕ) : derivative (Hr (n + 1)) = ((n : Polynomial ℝ) + 1) * Hr n := by
  induction n with
  | zero => simp [Hr_one, Hr_zero]
  | succ n ih =>
      rw [Hr_succ (n + 1), derivative_sub, derivative_mul, ih]
      simp only [derivative_X, one_mul, derivative_mul, derivative_add, derivative_natCast,
        derivative_one, zero_add, add_zero, zero_mul]
      rw [Hr_succ n]
      push_cast
      ring

/-- The Hermite differential equation `Heₙ'' = X Heₙ' - n Heₙ`. -/
