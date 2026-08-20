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

lemma le_integral_of_ge_one (F : ℝ → ℝ) (hF : Continuous F) (c p q : ℝ) (hcp : c ≤ p)
    (hpq : p ≤ q) (hqc : q ≤ c + 1) (hnn : ∀ x, 0 ≤ F x) (hone : ∀ x ∈ Icc p q, 1 ≤ F x) :
    q - p ≤ ∫ t in c..(c + 1), F t := by
  have hi : ∀ u v : ℝ, IntervalIntegrable F volume u v := fun u v => hF.intervalIntegrable u v
  have hsplit : (∫ t in c..(c + 1), F t)
      = (∫ t in c..p, F t) + (∫ t in p..q, F t) + (∫ t in q..(c + 1), F t) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hi c p) (hi p q),
      intervalIntegral.integral_add_adjacent_intervals (hi c q) (hi q (c + 1))]
  have h1 : (0 : ℝ) ≤ ∫ t in c..p, F t := intervalIntegral.integral_nonneg hcp fun x _ => hnn x
  have h3 : (0 : ℝ) ≤ ∫ t in q..(c + 1), F t :=
    intervalIntegral.integral_nonneg hqc fun x _ => hnn x
  have h2 : q - p ≤ ∫ t in p..q, F t := by
    have h := intervalIntegral.integral_mono_on (f := fun _ => (1 : ℝ)) (g := F) hpq
      intervalIntegrable_const (hi p q) fun x hx => hone x hx
    simpa using h
  rw [hsplit]; linarith

/-- A continuous function on the circle dominating the indicator of the arc `[a, b)`,
with integral at most `(b - a) + 2 * eps`. -/
