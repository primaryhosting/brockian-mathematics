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

theorem willmoreEnergy_torusOfRevolution (hr : 0 < r) (hR : r < R) :
    (torusOfRevolution R r).willmoreEnergy = π ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hRr : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hs0 : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.mpr hRr
  have hinner : ∀ v : ℝ, (∫ u in (0 : ℝ)..(2 * π),
      (torusOfRevolution R r).meanCurvature u v ^ 2 * (torusOfRevolution R r).areaElement u v)
      = π * R ^ 2 / (2 * r * Real.sqrt (R ^ 2 - r ^ 2)) := by
    intro v
    rw [show (fun u : ℝ => (torusOfRevolution R r).meanCurvature u v ^ 2 *
        (torusOfRevolution R r).areaElement u v)
        = fun u : ℝ => (R + 2 * r * cos u) ^ 2 / (4 * r * (R + r * cos u)) from
      funext fun u => torus_integrand hr hR u v]
    exact torus_u_integral hr hR
  rw [ParamSurface.willmoreEnergy]
  rw [intervalIntegral.integral_congr (g := fun _ : ℝ => π * R ^ 2 / (2 * r * Real.sqrt (R ^ 2 - r ^ 2)))
    (fun v _ => hinner v)]
  rw [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

end TorusIntegral

/-! ## The Willmore conjecture for tori of revolution -/

/-- The lower bound `2π²` for the energy of a torus of revolution, with the equality case. -/
