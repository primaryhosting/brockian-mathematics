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

theorem areaElt_eq (R r u v : ℝ) (hr : 0 < r) (hD : 0 < R + r * Real.cos u) :
    areaElt R r u v = r * (R + r * Real.cos u) := by
  have : firstE R r u v * firstG R r u v - firstF R r u v ^ 2
      = (r * (R + r * Real.cos u)) ^ 2 := by
    rw [firstE_eq, firstF_eq, firstG_eq]; ring
  rw [areaElt, this, Real.sqrt_sq (by positivity)]

/-- The pointwise Willmore integrand `H² dA` of the torus of revolution. -/
