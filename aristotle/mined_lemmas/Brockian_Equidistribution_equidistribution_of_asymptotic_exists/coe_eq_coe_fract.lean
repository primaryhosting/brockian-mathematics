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

theorem coe_eq_coe_fract (x : ℝ) :
    ((x : ℝ) : AddCircle (1 : ℝ)) = ((Int.fract x : ℝ) : AddCircle (1 : ℝ)) := by
  have h0 : (((⌊x⌋ : ℤ) : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨⌊x⌋, by simp⟩
  have h1 : ((Int.fract x : ℝ) : AddCircle (1 : ℝ))
      = (x : AddCircle (1 : ℝ)) - (((⌊x⌋ : ℤ) : ℝ) : AddCircle (1 : ℝ)) := by
    rw [Int.fract]
    exact QuotientAddGroup.mk_sub _ _ _
  rw [h1, h0, sub_zero]

/-! ## Counting visits to an interval -/

/-- The number of `n < N` for which the fractional part of `n * α` lies in `[a, b)`. -/
