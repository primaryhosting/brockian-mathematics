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

theorem integral_bump_le {c : AddCircle (1:ℝ)} {s δ : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s + δ) :
    ∫ t : AddCircle (1:ℝ), bump c s δ t ≤ min 1 (2*(s+δ)) := by
  have hle : ∀ x, bump c s δ x ≤ (closedBall c (s+δ)).indicator (1 : AddCircle (1:ℝ) → ℝ) x := by
    intro x
    by_cases hx : x ∈ closedBall c (s + δ)
    · rw [indicator_of_mem hx]; exact bump_le_one _ _ _ _
    · rw [indicator_of_notMem hx]
      by_contra h
      push_neg at h
      exact hx (by simpa [Metric.mem_closedBall] using (dist_lt_of_bump_pos hδ h).le)
  calc ∫ t : AddCircle (1:ℝ), bump c s δ t
      ≤ ∫ t : AddCircle (1:ℝ), (closedBall c (s+δ)).indicator (1 : AddCircle (1:ℝ) → ℝ) t :=
        integral_mono (integrable_bump c s δ) (integrable_indicator_closedBall c (s+δ)) hle
    _ = (volume : Measure (AddCircle (1:ℝ))).real (closedBall c (s+δ)) :=
        integral_indicator_one measurableSet_closedBall
    _ = min 1 (2*(s+δ)) := measureReal_closedBall c hs

/-- Lower bound for the integral of a bump function. -/
