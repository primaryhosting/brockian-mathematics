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

lemma He_succ (n : ℕ) : He (n + 1) = X * He n - derivative (He n) := by
  simp [He, Polynomial.hermite_succ, Polynomial.derivative_map]

