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

/-
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

open Filter Topology MeasureTheory Complex

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian.Equidistribution

/-! ## Weyl averages of continuous functions on the circle -/

/-- The `N`-th Weyl average of a continuous function `f` on the circle `ℝ / ℤ`, sampled along the
orbit `n ↦ n • α` of the rotation by `α`. -/

theorem circle_integral_sub_le (f g : C(AddCircle (1 : ℝ), ℂ)) :
    ‖(∫ x, f x) - ∫ x, g x‖ ≤ ‖f - g‖ := by
  have h : (∫ x, f x) - (∫ x, g x) = ∫ x, (f - g) x := by
    rw [← integral_sub (circle_integrable f) (circle_integrable g)]; simp
  rw [h]
  have := norm_integral_le_of_norm_le_const (μ := (volume : Measure (AddCircle (1 : ℝ))))
    (f := fun x => (f - g) x) (C := ‖f - g‖)
    (Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm _ _)
  simpa [measureReal_def] using this

/-- The set of continuous functions whose Weyl averages converge to their integral. -/
