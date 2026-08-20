import Brockian.EquidistributionBVReduction

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

import Mathlib

/-!
# Equidistribution of `n • α` and the reduction of configuration counts to the main term

For an irrational `α`, the configuration count

`configCount α a b N = #{ n < N : Int.fract (n * α) ∈ [a, b) }`

is asymptotic to its main term `mainTerm a b N = (b - a) * N`.

The analytic input (Weyl equidistribution of the sequence `n • α` on the circle `ℝ / ℤ`)
is proved here from scratch, so the final statement
`configCount_over_main_tendsto` is unconditional.

The proof proceeds by:
* computing the Birkhoff averages of the Fourier monomials `fourier k` along the orbit
  (geometric sums, `avg_fourier_tendsto`);
* extending to all continuous functions by Stone--Weierstrass (`avg_continuous_tendsto`);
* sandwiching the indicator of an arc between continuous piecewise-linear functions
  (a bounded-variation reduction) to obtain the counting asymptotics.
-/

open Filter MeasureTheory Set Topology Complex
open scoped BigOperators

set_option autoImplicit false

namespace Brockian

namespace EquidistributionBVReduction

noncomputable section

local instance isProbabilityMeasure_volume_unitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

/-- The point `n * α` of the circle `ℝ / ℤ`. -/

theorem avg_continuous_tendsto {alpha : ℝ} (halpha : Irrational alpha) (f : C(UnitAddCircle, ℂ)) :
    Tendsto (avg alpha f) atTop (𝓝 (∫ x : UnitAddCircle, f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := exists_trig_poly_approx f (ε := ε / 3) (by positivity)
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp (avg_span_tendsto halpha hg)) (ε / 3) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 : dist (avg alpha f N) (avg alpha g N) < ε / 3 := by
    rw [dist_eq_norm]; exact lt_of_le_of_lt (avg_sub_le alpha f g N) hfg
  have h2 : dist (avg alpha (g : UnitAddCircle → ℂ) N) (∫ x : UnitAddCircle, g x) < ε / 3 :=
    hN₀ N hN
  have h3 : dist (∫ x : UnitAddCircle, g x) (∫ x : UnitAddCircle, f x) < ε / 3 := by
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (integral_sub_le g f) ?_
    rwa [← norm_neg, neg_sub]
  calc dist (avg alpha f N) (∫ x : UnitAddCircle, f x)
      ≤ dist (avg alpha f N) (avg alpha g N)
        + dist (avg alpha (g : UnitAddCircle → ℂ) N) (∫ x : UnitAddCircle, g x)
        + dist (∫ x : UnitAddCircle, g x) (∫ x : UnitAddCircle, f x) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := by ring

/-- Real-valued version of `avg_continuous_tendsto`. -/
