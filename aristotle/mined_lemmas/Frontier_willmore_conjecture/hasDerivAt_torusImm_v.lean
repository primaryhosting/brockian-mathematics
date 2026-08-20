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

theorem hasDerivAt_torusImm_v (R r u v : ℝ) :
    HasDerivAt (fun t => torusImm R r u t)
      (-((R + r * Real.cos u) * Real.sin v), (R + r * Real.cos u) * Real.cos v, 0) v :=
  hasDerivAt_triple (by simpa using (Real.hasDerivAt_cos v).const_mul (R + r * Real.cos u))
    (by simpa using (Real.hasDerivAt_sin v).const_mul (R + r * Real.cos u)) (hasDerivAt_const _ _)

