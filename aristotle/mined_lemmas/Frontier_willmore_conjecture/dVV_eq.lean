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

theorem dVV_eq (R r u v : ℝ) :
    dVV R r u v =
      (-((R + r * Real.cos u) * Real.cos v), -((R + r * Real.cos u) * Real.sin v), 0) := by
  have hfun : (fun t => dV R r u t) =
      fun t => ((-((R + r * Real.cos u) * Real.sin t), (R + r * Real.cos u) * Real.cos t,
        0) : E3) := funext fun t => dV_eq R r u t
  rw [dVV, hfun]
  refine HasDerivAt.deriv (hasDerivAt_triple ?_ ?_ (hasDerivAt_const _ _))
  · simpa using ((Real.hasDerivAt_sin v).const_mul (R + r * Real.cos u)).neg
  · simpa using (Real.hasDerivAt_cos v).const_mul (R + r * Real.cos u)

/-! ### The fundamental forms of the torus of revolution -/

