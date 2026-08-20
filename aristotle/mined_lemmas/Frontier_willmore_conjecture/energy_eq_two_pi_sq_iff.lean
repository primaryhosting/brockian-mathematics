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

theorem energy_eq_two_pi_sq_iff (R r : ℝ) (hr : 0 < r) (hR : r < R) :
    π ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) = 2 * π ^ 2 ↔ R = Real.sqrt 2 * r := by
  have hr0 : (0:ℝ) < R := hr.trans hR
  have hpi : (0:ℝ) < π := Real.pi_pos
  set S := Real.sqrt (R ^ 2 - r ^ 2) with hSdef
  have hS0 : 0 < S := Real.sqrt_pos.2 (by nlinarith)
  have hSsq : S ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt (by nlinarith)
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hpi2 : (0:ℝ) < π ^ 2 := by positivity
  rw [div_eq_iff (by positivity)]
  constructor
  · intro h
    have hR2 : R ^ 2 = 2 * (r * S) :=
      mul_left_cancel₀ (ne_of_gt hpi2) (by linear_combination h)
    have hsq : R ^ 2 = 2 * r ^ 2 := by
      nlinarith [sq_nonneg (R ^ 2 - 2 * r ^ 2), mul_pos hr hS0]
    nlinarith [sq_nonneg (R - Real.sqrt 2 * r), mul_pos h2pos hr]
  · intro h
    subst h
    have hSval : S = r := by
      rw [hSdef, show (Real.sqrt 2 * r) ^ 2 - r ^ 2 = r ^ 2 by linear_combination r ^ 2 * h2]
      exact Real.sqrt_sq hr.le
    rw [hSval]
    linear_combination (π ^ 2 * r ^ 2) * h2

/-! ## Main statement -/

/--
**Willmore's theorem for tori of revolution** (the rotationally symmetric case of the
Willmore conjecture, proved in full generality by Marques and Neves).

For the torus of revolution in `ℝ³` with centre-circle radius `R` and tube radius `r`,
`0 < r < R`, whose mean curvature `H` and area element `dA` are computed here from the
first and second fundamental forms of the explicit immersion
`(u, v) ↦ ((R + r cos u) cos v, (R + r cos u) sin v, r sin u)`, the Willmore energy satisfies

`∫ H² dA ≥ 2π²`,

with equality if and only if `R = √2 · r`, i.e. exactly for the torus which is the
stereographic image of the Clifford torus in `S³`.
-/
