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

theorem fourier_ne_one {α : ℝ} (hα : Irrational α) {k : ℤ} (hk : k ≠ 0) :
    (fourier k ((α : ℝ) : AddCircle (1:ℝ))) ≠ 1 := by
  rw [fourier_coe_apply]
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨m, hm⟩ := h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : (2:ℂ) * (Real.pi:ℂ) * Complex.I ≠ 0 := by
    simp [hpi, Complex.I_ne_zero]
  have key : (k : ℂ) * (α : ℂ) = (m : ℂ) := by
    have : (2 * (Real.pi:ℂ) * Complex.I) * ((k:ℂ) * α)
        = (2 * (Real.pi:ℂ) * Complex.I) * m := by
      push_cast at hm ⊢
      linear_combination hm
    exact mul_left_cancel₀ h2 this
  have hreal : (k : ℝ) * α = (m : ℝ) := by exact_mod_cast key
  have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  refine hα ⟨(m : ℚ) / (k : ℚ), ?_⟩
  push_cast
  field_simp
  linear_combination -hreal

/-- `‖fourier k x‖ = 1`. -/
