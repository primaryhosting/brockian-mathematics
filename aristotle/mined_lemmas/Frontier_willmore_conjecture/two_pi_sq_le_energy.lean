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

theorem two_pi_sq_le_energy (R r : ℝ) (hr : 0 < r) (hR : r < R) :
    2 * π ^ 2 ≤ π ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hr0 : (0:ℝ) < R := hr.trans hR
  set S := Real.sqrt (R ^ 2 - r ^ 2) with hSdef
  have hS0 : 0 < S := Real.sqrt_pos.2 (by nlinarith)
  have hSsq : S ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt (by nlinarith)
  have hkey : 2 * (r * S) ≤ R ^ 2 := by
    nlinarith [sq_nonneg (R ^ 2 - 2 * r ^ 2), sq_nonneg (r * S), sq_nonneg (R ^ 2 - 2 * r * S),
      mul_pos hr hS0]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [Real.pi_pos, sq_nonneg π, mul_pos hr hS0]

/-- Equality in the Willmore bound holds exactly for the Clifford ratio `R = √2 r`. -/
