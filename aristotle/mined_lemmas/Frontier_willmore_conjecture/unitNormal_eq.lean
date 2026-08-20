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

theorem unitNormal_eq (R r u v : ℝ) (hr : 0 < r) (hD : 0 < R + r * Real.cos u) :
    unitNormal R r u v =
      (-(Real.cos u * Real.cos v), -(Real.cos u * Real.sin v), -Real.sin u) := by
  have hne : r * (R + r * Real.cos u) ≠ 0 := by positivity
  rw [unitNormal, nrm3_normalVec R r u v hr hD, normalVec_eq]
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp

