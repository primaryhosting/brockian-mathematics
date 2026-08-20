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

theorem normalVec_eq (R r u v : ℝ) :
    normalVec R r u v =
      (-(r * (R + r * Real.cos u) * Real.cos u * Real.cos v),
       -(r * (R + r * Real.cos u) * Real.cos u * Real.sin v),
       -(r * (R + r * Real.cos u) * Real.sin u)) := by
  have hv := Real.sin_sq_add_cos_sq v
  simp only [normalVec, cross3, dU_eq, dV_eq, Prod.mk.injEq]
  exact ⟨by ring, by ring, by linear_combination (-(r * (R + r * Real.cos u) * Real.sin u)) * hv⟩

