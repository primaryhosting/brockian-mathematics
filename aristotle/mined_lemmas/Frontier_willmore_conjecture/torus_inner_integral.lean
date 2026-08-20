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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## Basic vector algebra in `ℝ³` -/

/-- Euclidean three-space, as a triple of reals. -/
abbrev R3 := ℝ × ℝ × ℝ

/-- The standard inner product on `ℝ³`. -/

lemma torus_inner_integral {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    (∫ u in (0:ℝ)..(2 * Real.pi), (R + 2 * r * Real.cos u) ^ 2 / (4 * r * (R + r * Real.cos u)))
      = Real.pi * R ^ 2 / (2 * r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hr' : r ≠ 0 := ne_of_gt hr
  have hs_pos : 0 < Real.sqrt (R ^ 2 - r ^ 2) := sqrt_sq_sub_pos hr hR
  have hs' : Real.sqrt (R ^ 2 - r ^ 2) ≠ 0 := ne_of_gt hs_pos
  have hcongr : (∫ u in (0:ℝ)..(2 * Real.pi),
      (R + 2 * r * Real.cos u) ^ 2 / (4 * r * (R + r * Real.cos u)))
      = (1 / (4 * r)) * ∫ u in (0:ℝ)..(2 * Real.pi),
        (R + 2 * r * Real.cos u) ^ 2 / (R + r * Real.cos u) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    have hp' : R + r * Real.cos u ≠ 0 := ne_of_gt (torus_radius_pos hr hR u)
    field_simp
  rw [hcongr]
  have hFTC : (∫ u in (0:ℝ)..(2 * Real.pi),
      (R + 2 * r * Real.cos u) ^ 2 / (R + r * Real.cos u))
      = torusAntider R r (2 * Real.pi) - torusAntider R r 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro u _
      exact torusAntider_hasDerivAt hr hR u
    · exact (torus_integrand_continuous hr hR).intervalIntegrable _ _
  rw [hFTC]
  simp only [torusAntider, Real.sin_two_pi, Real.sin_zero, Real.cos_zero]
  simp only [mul_zero, zero_div, Real.arctan_zero, sub_zero, add_zero, zero_add]
  field_simp
  ring

/-! ### The Willmore energy of a torus of revolution -/

/-- The Willmore energy of the torus of revolution with radii `R > r > 0` equals
`π² R² / (r √(R² - r²))`. -/
