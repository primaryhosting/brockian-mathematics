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

theorem weylGood_closed (α : ℝ) :
    IsClosed ((weylGood α : Submodule ℂ C(AddCircle (1 : ℝ), ℂ)) :
      Set C(AddCircle (1 : ℝ), ℂ)) := by
  refine isClosed_of_closure_subset fun f hf => ?_
  show Tendsto (weylAvg α f) atTop (𝓝 (∫ x, f x))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hgS, hfg⟩ := Metric.mem_closure_iff.mp hf (ε / 3) (by linarith)
  have hgmem : Tendsto (weylAvg α g) atTop (𝓝 (∫ x, g x)) := hgS
  rw [Metric.tendsto_atTop] at hgmem
  obtain ⟨N₀, hN₀⟩ := hgmem (ε / 3) (by linarith)
  refine ⟨N₀, fun N hN => ?_⟩
  have hnorm : ‖f - g‖ < ε / 3 := by rwa [← dist_eq_norm]
  have hnorm' : ‖g - f‖ < ε / 3 := by rw [← dist_eq_norm, dist_comm]; exact hfg
  have d1 : dist (weylAvg α f N) (weylAvg α g N) < ε / 3 := by
    rw [dist_eq_norm]; linarith [weylAvg_sub_le α f g N]
  have d3 : dist (∫ x, g x) (∫ x, f x) < ε / 3 := by
    rw [dist_eq_norm]; linarith [circle_integral_sub_le g f]
  have d2 := hN₀ N hN
  calc dist (weylAvg α f N) (∫ x, f x)
      ≤ dist (weylAvg α f N) (weylAvg α g N) + dist (weylAvg α g N) (∫ x, g x)
        + dist (∫ x, g x) (∫ x, f x) := dist_triangle4 _ _ _ _
    _ < ε := by linarith

/-! ## The Weyl exponential sums -/

