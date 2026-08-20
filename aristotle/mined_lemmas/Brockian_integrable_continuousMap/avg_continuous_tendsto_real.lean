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

theorem avg_continuous_tendsto_real {alpha : ℝ} (halpha : Irrational alpha)
    (f : C(UnitAddCircle, ℝ)) :
    Tendsto (avg alpha f) atTop (𝓝 (∫ x : UnitAddCircle, f x)) := by
  set F : C(UnitAddCircle, ℂ) := ⟨fun x => ((f x : ℝ) : ℂ), by fun_prop⟩ with hF
  have hint : (∫ x : UnitAddCircle, F x) = ((∫ x : UnitAddCircle, f x : ℝ) : ℂ) := by
    simp only [hF, ContinuousMap.coe_mk]
    exact integral_complex_ofReal
  have havg : avg alpha (F : UnitAddCircle → ℂ) = fun N => ((avg alpha f N : ℝ) : ℂ) := by
    funext N
    simp [avg, hF, Complex.ofReal_sum, Complex.real_smul]
  have h := avg_continuous_tendsto halpha F
  rw [hint, havg] at h
  have h2 := (Complex.continuous_re.tendsto _).comp h
  simpa [Function.comp] using h2

/-! ### Continuous sandwich functions for the indicator of an arc -/

/-- A trapezoidal function which equals `1` on `[a, b]` and vanishes outside `[a - eps, b + eps]`. -/
