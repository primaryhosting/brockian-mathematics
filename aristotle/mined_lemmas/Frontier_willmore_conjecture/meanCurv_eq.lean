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

theorem meanCurv_eq (R r u v : ℝ) (hr : 0 < r) (hD : 0 < R + r * Real.cos u) :
    meanCurv R r u v = (R + 2 * r * Real.cos u) / (2 * r * (R + r * Real.cos u)) := by
  have hne : r ≠ 0 := ne_of_gt hr
  have hDne : R + r * Real.cos u ≠ 0 := ne_of_gt hD
  simp only [meanCurv, firstE_eq, firstF_eq, firstG_eq, secondE_eq R r u v hr hD,
    secondF_eq R r u v hr hD, secondG_eq R r u v hr hD]
  field_simp
  ring

/-- The area element of the torus of revolution: `dA = r (R + r cos u) du dv`. -/
