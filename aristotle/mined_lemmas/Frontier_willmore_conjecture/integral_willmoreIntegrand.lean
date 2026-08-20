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

theorem integral_willmoreIntegrand (R r : ℝ) (hr : 0 < r) (hR : r < R) :
    (∫ u in (0:ℝ)..(2 * π), (R + 2 * r * Real.cos u) ^ 2 / (4 * r * (R + r * Real.cos u)))
      = π * R ^ 2 / (2 * r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hr0 : (0:ℝ) < R := hr.trans hR
  have hS0 : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_willmorePrimitive R r hr hR x)
    ((continuous_willmoreIntegrand R r hr hR).intervalIntegrable _ _)]
  simp only [willmorePrimitive, Real.sin_two_pi, Real.cos_two_pi, Real.sin_zero, Real.cos_zero]
  rw [show r * (0:ℝ) / (R + Real.sqrt (R ^ 2 - r ^ 2) + r * 1) = 0 by ring]
  simp only [Real.arctan_zero, mul_zero, sub_zero, zero_add]
  have hrne : r ≠ 0 := ne_of_gt hr
  have hSne : Real.sqrt (R ^ 2 - r ^ 2) ≠ 0 := ne_of_gt hS0
  field_simp
  ring

/-- **The Willmore energy of the torus of revolution.**
For radii `0 < r < R`, `∫ H² dA = π² R² / (r √(R² - r²))`. -/
