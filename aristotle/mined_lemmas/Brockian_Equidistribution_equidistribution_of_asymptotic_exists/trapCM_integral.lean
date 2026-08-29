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

theorem trapCM_integral (a b δ : ℝ) (hδ : 0 < δ) (ha : 0 ≤ a) (hb : b ≤ 1) :
    (∫ x : AddCircle (1 : ℝ), trapCM a b δ hδ ha hb x) = ∫ x in (0 : ℝ)..1, trap a b δ x := by
  have hf : trap a b δ 0 = trap a b δ (0 + 1) := by
    rw [zero_add, trap_eq_zero_of_le a b δ 0 hδ ha, trap_eq_zero_of_ge a b δ 1 hδ hb]
  show (∫ x : AddCircle (1 : ℝ), AddCircle.liftIco 1 0 (trap a b δ) x) = _
  rw [← AddCircle.liftIoc_eq_liftIco hf, AddCircle.integral_liftIoc_eq_intervalIntegral]
  norm_num

