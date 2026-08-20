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

theorem total_over_main_tendsto_of_monotoneOn {α : ℝ} (hα : Irrational α) {f : ℝ → ℝ}
    (hf : MonotoneOn f (Icc 0 1)) (hI : (∫ t in (0:ℝ)..1, f t) ≠ 0) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, f (Int.fract (n * α)))
        / ((N:ℝ) * ∫ t in (0:ℝ)..1, f t)) atTop (𝓝 1) := by
  have h := monotoneOn_avg_tendsto (equidistributed_irrational hα) hf
  have h2 := h.div_const (∫ t in (0:ℝ)..1, f t)
  rw [div_self hI] at h2
  exact h2.congr (fun N => by rw [div_div])

/-- A concrete instance: the fractional parts of `nα` have average `1/2`. -/
