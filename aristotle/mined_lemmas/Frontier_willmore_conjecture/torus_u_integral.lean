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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Real

/-! ## Partial derivatives of functions of two real variables -/

/-- Partial derivative with respect to the first variable. -/

lemma torus_u_integral (hr : 0 < r) (hR : r < R) :
    (∫ u in (0 : ℝ)..(2 * π), (R + 2 * r * cos u) ^ 2 / (4 * r * (R + r * cos u)))
      = π * R ^ 2 / (2 * r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hRr : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hs0 : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.mpr hRr
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_torusPrimitive hr hR x)
      ((torus_integrand_continuous hr hR).intervalIntegrable _ _)]
  simp only [torusPrimitive, Real.sin_two_pi, Real.cos_two_pi, Real.sin_zero, Real.cos_zero]
  rw [show (r : ℝ) * 0 = 0 by ring]
  simp only [zero_div, Real.arctan_zero]
  field_simp
  ring

/-- **The Willmore energy of the torus of revolution.** -/
