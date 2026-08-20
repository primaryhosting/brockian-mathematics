/-
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial

namespace Frontier

noncomputable section

/-! ## Hermite polynomials over `ℝ` -/

/-- The `n`-th probabilists' Hermite polynomial, viewed as a real polynomial. -/

lemma derivative_hermite_succ (n : ℕ) :
    derivative (Polynomial.hermite (n + 1)) = C ((n : ℤ) + 1) * Polynomial.hermite n := by
  induction n with
  | zero => simp [Polynomial.hermite_one]
  | succ n ih =>
      rw [Polynomial.hermite_succ (n + 1), derivative_sub, derivative_mul, derivative_X, ih]
      rw [derivative_mul, derivative_C, Polynomial.hermite_succ n]
      push_cast
      ring
  
