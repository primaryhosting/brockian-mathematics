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

noncomputable def landauLength (hbar m omegac : ℝ) : ℝ := Real.sqrt (hbar / (2 * m * omegac))

/-- The `n`-th Landau eigenfunction (transverse factor, in the Landau gauge):
`He_n (y/ℓ) exp (-(y/ℓ)²/4)`. -/
