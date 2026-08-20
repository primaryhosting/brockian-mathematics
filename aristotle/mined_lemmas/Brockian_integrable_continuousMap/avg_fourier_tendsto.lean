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

theorem avg_fourier_tendsto {alpha : ℝ} (halpha : Irrational alpha) (k : ℤ) :
    Tendsto (avg alpha (fourier (T := 1) k)) atTop
      (𝓝 (∫ x : UnitAddCircle, fourier (T := 1) k x)) := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [integral_fourier_eq, if_pos rfl]
    have hev : ∀ N : ℕ, N ≠ 0 → avg alpha (fourier (T := 1) 0) N = 1 := by
      intro N hN
      have hN' : ((N : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
      simp only [avg, fourier_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rw [Complex.real_smul]
      push_cast
      field_simp
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ne_atTop 0] with N hN
    exact (hev N hN).symm
  · rw [integral_fourier_eq, if_neg hk]
    exact avg_fourier_tendsto_zero halpha hk

/-! ### From monomials to all continuous functions -/

