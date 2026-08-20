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

lemma He_derivative_succ (n : ℕ) : derivative (He (n + 1)) = C ((n : ℝ) + 1) * He n := by
  simp only [He, ← Polynomial.derivative_map, derivative_hermite_succ]
  simp

/-- Hermite's differential equation: `He'' - x He' + n He = 0`. -/
