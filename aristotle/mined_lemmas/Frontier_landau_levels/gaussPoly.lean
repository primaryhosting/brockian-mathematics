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

noncomputable def gaussPoly (P : Polynomial ℝ) (x : ℝ) : ℝ :=
  P.eval x * Real.exp (-(x ^ 2 / 4))

/-- The derivative operator maps `gaussPoly P` to `gaussPoly (P' - x P / 2)`. -/
