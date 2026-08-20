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

theorem avg_tendsto_of_mem_span {α : ℝ} (hα : Irrational α) (F : C(AddCircle (1:ℝ), ℂ))
    (hF : F ∈ Submodule.span ℂ (Set.range (fourier (T := (1:ℝ))))) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, F ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ)) atTop
      (𝓝 (∫ t : AddCircle (1:ℝ), F t)) := by
  induction hF using Submodule.span_induction with
  | mem F hF => obtain ⟨k, rfl⟩ := hF; exact avg_fourier_tendsto hα k
  | zero => simp
  | add F G _ _ ihF ihG =>
      have hint : ∫ t : AddCircle (1:ℝ), (F + G) t
          = (∫ t : AddCircle (1:ℝ), F t) + ∫ t : AddCircle (1:ℝ), G t := by
        simp only [ContinuousMap.add_apply]
        exact integral_add (integrable_of_continuousMap F) (integrable_of_continuousMap G)
      rw [hint]
      refine (ihF.add ihG).congr (fun N => ?_)
      simp only [ContinuousMap.add_apply, sum_add_distrib]
      ring
  | smul c F _ ih =>
      have hint : ∫ t : AddCircle (1:ℝ), (c • F) t = c * ∫ t : AddCircle (1:ℝ), F t := by
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        exact integral_const_mul c _
      rw [hint]
      refine (ih.const_mul c).congr (fun N => ?_)
      simp only [ContinuousMap.smul_apply, smul_eq_mul, ← mul_sum]
      ring

/-- The integral of a continuous function on the unit circle is bounded by its sup-norm. -/
