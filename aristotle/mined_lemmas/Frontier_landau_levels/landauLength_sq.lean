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

theorem landauLength_sq {hbar m omegac : ℝ} (hh : 0 < hbar) (hm : 0 < m) (hw : 0 < omegac) :
    (landauLength hbar m omegac) ^ 2 = hbar / (2 * m * omegac) := by
  have : (0:ℝ) ≤ hbar / (2 * m * omegac) := by positivity
  simpa [landauLength] using Real.sq_sqrt this

