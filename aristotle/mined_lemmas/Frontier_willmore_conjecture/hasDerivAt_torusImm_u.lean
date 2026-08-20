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

theorem hasDerivAt_torusImm_u (R r v u : ℝ) :
    HasDerivAt (fun t => torusImm R r t v)
      (-(r * Real.sin u) * Real.cos v, -(r * Real.sin u) * Real.sin v, r * Real.cos u) u := by
  have h1 : HasDerivAt (fun t => R + r * Real.cos t) (-(r * Real.sin u)) u := by
    simpa using ((Real.hasDerivAt_cos u).const_mul r).const_add R
  exact hasDerivAt_triple (h1.mul_const _) (h1.mul_const _)
    (by simpa using (Real.hasDerivAt_sin u).const_mul r)

