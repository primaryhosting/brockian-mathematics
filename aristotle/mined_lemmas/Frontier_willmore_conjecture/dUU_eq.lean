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

theorem dUU_eq (R r u v : ℝ) :
    dUU R r u v =
      (-(r * Real.cos u) * Real.cos v, -(r * Real.cos u) * Real.sin v, -(r * Real.sin u)) := by
  have hfun : (fun t => dU R r t v) =
      fun t => ((-(r * Real.sin t) * Real.cos v, -(r * Real.sin t) * Real.sin v,
        r * Real.cos t) : E3) := funext fun t => dU_eq R r t v
  have h1 : HasDerivAt (fun t => -(r * Real.sin t)) (-(r * Real.cos u)) u := by
    simpa using ((Real.hasDerivAt_sin u).const_mul r).neg
  rw [dUU, hfun]
  exact (hasDerivAt_triple (h1.mul_const _) (h1.mul_const _)
    (by simpa using (Real.hasDerivAt_cos u).const_mul r)).deriv

