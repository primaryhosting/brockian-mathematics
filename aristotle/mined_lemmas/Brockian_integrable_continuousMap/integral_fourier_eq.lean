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

theorem integral_fourier_eq (k : ℤ) :
    (∫ x : UnitAddCircle, fourier (T := 1) k x) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp
  rw [← UnitAddCircle.intervalIntegral_preimage 0 (fun x => fourier (T := 1) k x)]
  have h : ∀ x : ℝ, (fourier (T := 1) k (x : UnitAddCircle))
      = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * k) * x) := by
    intro x
    rw [fourier_coe_apply]
    push_cast
    ring_nf
  simp only [h]
  have hc : (2 * (Real.pi : ℂ) * Complex.I * k) ≠ 0 := by
    simp [Complex.ext_iff, Real.pi_ne_zero, hk]
  rw [integral_exp_mul_complex hc]
  have h1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * k * ((0 + 1 : ℝ) : ℂ)) = 1 := by
    push_cast
    rw [show (2 * (Real.pi : ℂ) * Complex.I * k * (0 + 1)) = (k : ℂ) * (2 * Real.pi * Complex.I) by
      ring]
    exact Complex.exp_int_mul_two_pi_mul_I k
  rw [h1]
  simp

/-- Weyl's exponential-sum estimate: for `k ≠ 0` the Birkhoff averages of `fourier k` along
the orbit of an irrational rotation tend to `0`. -/
