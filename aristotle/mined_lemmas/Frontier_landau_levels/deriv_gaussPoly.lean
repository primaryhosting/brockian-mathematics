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

lemma deriv_gaussPoly (P : Polynomial ℝ) :
    deriv (gaussPoly P) = gaussPoly (derivative P - C (1 / 2 : ℝ) * X * P) :=
  funext fun x => (hasDerivAt_gaussPoly P x).deriv

/-! ## Landau levels -/

/-- The `n`-th Landau/oscillator eigenstate (in dimensionless coordinates). -/
