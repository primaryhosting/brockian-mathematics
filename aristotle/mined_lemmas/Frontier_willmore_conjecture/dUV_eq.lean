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

theorem dUV_eq (R r u v : ℝ) :
    dUV R r u v = (r * Real.sin u * Real.sin v, -(r * Real.sin u) * Real.cos v, 0) := by
  have hfun : (fun t => dU R r u t) =
      fun t => ((-(r * Real.sin u) * Real.cos t, -(r * Real.sin u) * Real.sin t,
        r * Real.cos u) : E3) := funext fun t => dU_eq R r u t
  rw [dUV, hfun]
  refine HasDerivAt.deriv (hasDerivAt_triple ?_ ?_ (hasDerivAt_const _ _))
  · simpa [mul_comm] using (Real.hasDerivAt_cos v).const_mul (-(r * Real.sin u))
  · simpa using (Real.hasDerivAt_sin v).const_mul (-(r * Real.sin u))

