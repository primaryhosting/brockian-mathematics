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

theorem willmoreEnergyRotational_eq (R r : ℝ) (hr : 0 < r) (hR : r < R) :
    willmoreEnergyRotational R r = π ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hr0 : (0:ℝ) < R := hr.trans hR
  have hS0 : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hinner : ∀ v : ℝ,
      (∫ u in (0:ℝ)..(2 * π), meanCurv R r u v ^ 2 * areaElt R r u v)
        = π * R ^ 2 / (2 * r * Real.sqrt (R ^ 2 - r ^ 2)) := by
    intro v
    rw [intervalIntegral.integral_congr
      (g := fun u => (R + 2 * r * Real.cos u) ^ 2 / (4 * r * (R + r * Real.cos u)))
      (fun u _ => integrand_eq R r u v hr (by nlinarith [Real.neg_one_le_cos u]))]
    exact integral_willmoreIntegrand R r hr hR
  rw [willmoreEnergyRotational]
  simp only [hinner]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have hrne : r ≠ 0 := ne_of_gt hr
  have hSne : Real.sqrt (R ^ 2 - r ^ 2) ≠ 0 := ne_of_gt hS0
  field_simp

/-! ## The sharp lower bound: the Clifford ratio `R = √2 r` -/

/-- The sharp lower bound `π² R² / (r √(R² - r²)) ≥ 2π²` for `0 < r < R`. -/
