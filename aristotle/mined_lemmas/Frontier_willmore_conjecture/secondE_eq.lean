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

theorem secondE_eq (R r u v : ℝ) (hr : 0 < r) (hD : 0 < R + r * Real.cos u) :
    secondE R r u v = r := by
  have hu := Real.sin_sq_add_cos_sq u
  have hv := Real.sin_sq_add_cos_sq v
  simp only [secondE, dot3, dUU_eq, unitNormal_eq R r u v hr hD]
  linear_combination (r * Real.cos u ^ 2) * hv + r * hu

