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

theorem willmoreEnergy_torusParam {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    willmoreEnergy (torusParam R r) =
      Real.pi ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hr' : r ≠ 0 := ne_of_gt hr
  have hs_pos : 0 < Real.sqrt (R ^ 2 - r ^ 2) := sqrt_sq_sub_pos hr hR
  have hs' : Real.sqrt (R ^ 2 - r ^ 2) ≠ 0 := ne_of_gt hs_pos
  have hinner : ∀ v : ℝ, (∫ u in (0:ℝ)..(2 * Real.pi),
      (meanCurvature (torusParam R r) u v) ^ 2 * areaElement (torusParam R r) u v)
      = Real.pi * R ^ 2 / (2 * r * Real.sqrt (R ^ 2 - r ^ 2)) := by
    intro v
    rw [show (∫ u in (0:ℝ)..(2 * Real.pi),
        (meanCurvature (torusParam R r) u v) ^ 2 * areaElement (torusParam R r) u v)
        = ∫ u in (0:ℝ)..(2 * Real.pi),
          (R + 2 * r * Real.cos u) ^ 2 / (4 * r * (R + r * Real.cos u)) from
      intervalIntegral.integral_congr (fun u _ => torus_integrand hr hR u v)]
    exact torus_inner_integral hr hR
  rw [willmoreEnergy]
  simp only [hinner]
  rw [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

/-! ### The sharp inequality -/

/-- Sharp lower bound behind the Willmore inequality: `2 r √(R² - r²) ≤ R²`. -/
