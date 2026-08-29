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

theorem deriv_landauState (hbar m omegac : ℝ) (n : ℕ) :
    deriv (landauState hbar m omegac n)
      = fun y => (1 / landauLength hbar m omegac) *
          hermiteGauss' n (y / landauLength hbar m omegac) := by
  funext y
  have hin : HasDerivAt (fun z : ℝ => z / landauLength hbar m omegac)
      (1 / landauLength hbar m omegac) y := by
    simpa using (hasDerivAt_id y).div_const (landauLength hbar m omegac)
  have := (hasDerivAt_hermiteGauss n (y / landauLength hbar m omegac)).comp y hin
  exact (this.congr_deriv (by ring)).deriv

