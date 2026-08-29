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

theorem hasDerivAt_gauss (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2 / 4)) (-(x / 2) * Real.exp (-x ^ 2 / 4)) x := by
  have h : HasDerivAt (fun y : ℝ => -y ^ 2 / 4) (-(x / 2)) x := by
    have := ((hasDerivAt_pow 2 x).neg).div_const 4
    simpa using this.congr_deriv (by ring)
  exact h.exp.congr_deriv (by ring)

