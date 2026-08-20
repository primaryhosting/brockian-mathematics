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
# Equidistribution of irrational rotations and the bounded-variation reduction

This file develops, from scratch, Weyl's equidistribution theorem for the sequence
`n ↦ n • α mod 1` (`α` irrational) and reduces averages of functions of bounded variation
to their integral.

The final result `total_over_main_tendsto` states that, for a function `f` of bounded
variation on `[0,1]` with nonzero integral, the *total*
`∑_{n < N} f (fract (n α))` divided by the *main term* `N * ∫₀¹ f` tends to `1`.
-/

open Filter Finset Set MeasureTheory Metric
open scoped Topology

namespace Brockian.EquidistributionBVReduction

noncomputable section

/-- A sequence of reals is equidistributed mod one when, for every subinterval `[a,b) ⊆ [0,1]`,
the proportion of the first `N` fractional parts lying in `[a, b)` tends to `b - a`. -/

theorem integral_fourier (k : ℤ) :
    ∫ t : AddCircle (1:ℝ), fourier k t = if k = 0 then 1 else 0 := by
  have h0 := congrFun (fourierCoeff_fourier (T := (1:ℝ)) k) 0
  simp only [fourierCoeff, neg_zero, fourier_zero, one_smul] at h0
  have hh : ∫ t : AddCircle (1:ℝ), fourier k t ∂AddCircle.haarAddCircle
      = ∫ t : AddCircle (1:ℝ), fourier k t := by
    rw [AddCircle.integral_haarAddCircle]; simp
  rw [← hh, h0]
  by_cases hk : k = 0 <;> simp [hk, Pi.single_apply, eq_comm]

/-- The Cesàro average of a Fourier character along the orbit converges to its integral. -/
