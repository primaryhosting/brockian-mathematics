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

lemma hasDerivAt_gaussPoly (P : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (gaussPoly P) (gaussPoly (derivative P - C (1 / 2 : ℝ) * X * P) x) x := by
  have h1 : HasDerivAt (fun y : ℝ => P.eval y) ((derivative P).eval x) x := P.hasDerivAt x
  have h2 : HasDerivAt (fun y : ℝ => -(y ^ 2 / 4)) (-(x / 2)) x := by
    have : HasDerivAt (fun y : ℝ => y ^ 2 / 4) (2 * x / 4) x := by
      simpa using ((hasDerivAt_pow 2 x).div_const 4)
    simpa [neg_div] using this.neg.congr_deriv (by ring)
  have h3 : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / 4)))
      (-(x / 2) * Real.exp (-(x ^ 2 / 4))) x := by
    simpa [mul_comm] using h2.exp
  have := h1.mul h3
  refine this.congr_deriv ?_
  simp [gaussPoly]
  ring

