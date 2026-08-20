import Mathlib

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

open MeasureTheory intervalIntegral

/-- The Berry curvature `F₁₂ = ∂₁A₂ - ∂₂A₁` of a Berry connection `A = (A₁, A₂)` on the
Brillouin zone, given the two partial derivatives `d1A2 = ∂₁A₂` and `d2A1 = ∂₂A₁`. -/

theorem tknn_chern_hall_landau_gauge (n : ℤ) (e h : ℝ) :
    chernNumber (berryCurvature (fun _ _ => 2 * Real.pi * (n : ℝ)) (fun _ _ => 0)) = (n : ℝ) ∧
      hallConductance (berryCurvature (fun _ _ => 2 * Real.pi * (n : ℝ)) (fun _ _ => 0)) e h
        = (n : ℝ) * (e ^ 2 / h) := by
  refine tknn_chern_hall (A1 := fun _ _ => 0) (A2 := fun x _ => 2 * Real.pi * (n : ℝ) * x)
    (n := n) e h ?_ ?_ ?_ ?_ ?_ ?_
  · intro x y
    simpa using (hasDerivAt_id x).const_mul (2 * Real.pi * (n : ℝ))
  · intro x y
    simpa using (hasDerivAt_const y (0 : ℝ))
  · exact continuous_const
  · exact continuous_const
  · intro x; rfl
  · intro y; ring

end Frontier

