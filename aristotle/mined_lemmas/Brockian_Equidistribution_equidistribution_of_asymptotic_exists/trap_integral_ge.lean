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

theorem trap_integral_ge (a b δ : ℝ) (hδ : 0 < δ) (ha : 0 ≤ a) (hb : b ≤ 1)
    (hab : a + δ ≤ b - δ) : (b - a) - 2 * δ ≤ ∫ x in (0 : ℝ)..1, trap a b δ x := by
  have hc : Continuous (trap a b δ) := trap_continuous a b δ
  have hint : ∀ u v : ℝ, IntervalIntegrable (trap a b δ) volume u v :=
    fun u v => hc.intervalIntegrable u v
  have h1 : (0 : ℝ) ≤ a + δ := by linarith
  have h2 : b - δ ≤ 1 := by linarith
  have hsplit : (∫ x in (0 : ℝ)..1, trap a b δ x)
      = (∫ x in (0 : ℝ)..(a + δ), trap a b δ x) + (∫ x in (a + δ)..(b - δ), trap a b δ x)
        + ∫ x in (b - δ)..1, trap a b δ x := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  have hmid : (∫ x in (a + δ)..(b - δ), trap a b δ x) = (b - δ) - (a + δ) := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) ?_]
    · simp
    · intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact trap_eq_one a b δ x hδ hx.1 hx.2
  have hl : 0 ≤ ∫ x in (0 : ℝ)..(a + δ), trap a b δ x :=
    intervalIntegral.integral_nonneg h1 fun x _ => trap_nonneg _ _ _ _
  have hr : 0 ≤ ∫ x in (b - δ)..1, trap a b δ x :=
    intervalIntegral.integral_nonneg h2 fun x _ => trap_nonneg _ _ _ _
  rw [hsplit, hmid]
  linarith

/-- The trapezoidal function, viewed as a continuous function on the circle `ℝ / ℤ`. -/
