/-
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Frontier

/-! ## Euclidean 3-space as `ℝ × ℝ × ℝ`

We use the plain product type and equip it with an explicit dot product and cross
product, so that all differential-geometric quantities below are literally the
classical ones. -/

/-- Ambient space `ℝ³`. -/
abbrev E3 := ℝ × ℝ × ℝ

/-- The Euclidean dot product on `ℝ³`. -/

theorem integrand_eq (R r u v : ℝ) (hr : 0 < r) (hD : 0 < R + r * Real.cos u) :
    meanCurv R r u v ^ 2 * areaElt R r u v
      = (R + 2 * r * Real.cos u) ^ 2 / (4 * r * (R + r * Real.cos u)) := by
  have hne : r ≠ 0 := ne_of_gt hr
  have hDne : R + r * Real.cos u ≠ 0 := ne_of_gt hD
  rw [meanCurv_eq R r u v hr hD, areaElt_eq R r u v hr hD]
  field_simp
  ring


/-! ## The Willmore energy of the torus of revolution

We integrate `H² dA` explicitly.  The antiderivative

`Φ(u) = sin u + R² (u - 2 arctan (r sin u / (R + S + r cos u))) / (4 r S)`,  `S = √(R² - r²)`,

is smooth on all of `ℝ` (its denominator `R + S + r cos u` never vanishes), which lets us
apply the fundamental theorem of calculus on `[0, 2π]` without any splitting. -/

/-- A global antiderivative of the Willmore integrand `(R + 2r cos u)² / (4r(R + r cos u))`. -/
