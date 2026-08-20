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

theorem avg_span_tendsto {alpha : ℝ} (halpha : Irrational alpha) {g : C(UnitAddCircle, ℂ)}
    (hg : g ∈ Submodule.span ℂ (Set.range (fourier (T := 1)))) :
    Tendsto (avg alpha g) atTop (𝓝 (∫ x : UnitAddCircle, g x)) := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact avg_fourier_tendsto halpha k
  | zero =>
      have h1 : (avg alpha ((0 : C(UnitAddCircle, ℂ)) : UnitAddCircle → ℂ)) = fun _ => 0 := by
        funext N; simp [avg]
      rw [h1]
      simp
  | add x y hx hy ihx ihy =>
      have hint : (∫ t : UnitAddCircle, (x + y) t) = (∫ t, x t) + ∫ t, y t := by
        simp only [ContinuousMap.add_apply]
        exact integral_add (integrable_continuousMap x) (integrable_continuousMap y)
      rw [hint]
      have h2 : (avg alpha ((x + y : C(UnitAddCircle, ℂ)) : UnitAddCircle → ℂ))
          = fun N => avg alpha x N + avg alpha y N := by
        funext N
        simp [avg, ContinuousMap.add_apply, Finset.sum_add_distrib, smul_add]
      rw [h2]
      exact ihx.add ihy
  | smul c x hx ihx =>
      have hint : (∫ t : UnitAddCircle, (c • x) t) = c • ∫ t, x t := by
        simp only [ContinuousMap.smul_apply]
        exact integral_smul c _
      rw [hint]
      have h3 : (avg alpha ((c • x : C(UnitAddCircle, ℂ)) : UnitAddCircle → ℂ))
          = fun N => c • avg alpha x N := by
        funext N
        simp [avg, ContinuousMap.smul_apply, Finset.mul_sum]
        ring_nf
      rw [h3]
      exact ihx.const_smul c

/-- Stone--Weierstrass: trigonometric polynomials are uniformly dense. -/
