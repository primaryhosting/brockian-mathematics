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

theorem secondG_eq (R r u v : ℝ) (hr : 0 < r) (hD : 0 < R + r * Real.cos u) :
    secondG R r u v = (R + r * Real.cos u) * Real.cos u := by
  have hv := Real.sin_sq_add_cos_sq v
  simp only [secondG, dot3, dVV_eq, unitNormal_eq R r u v hr hD]
  linear_combination ((R + r * Real.cos u) * Real.cos u) * hv

/-- The mean curvature of the torus of revolution: `H = (R + 2r cos u) / (2 r (R + r cos u))`. -/
