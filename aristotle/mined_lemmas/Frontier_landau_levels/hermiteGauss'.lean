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

/-! ### Hermite polynomial facts -/

/-- The derivative of the `(n+1)`-st probabilists' Hermite polynomial. -/

noncomputable def hermiteGauss' (n : ℕ) (x : ℝ) : ℝ :=
  (aeval x (derivative (hermite n)) - x / 2 * He n x) * Real.exp (-x ^ 2 / 4)

