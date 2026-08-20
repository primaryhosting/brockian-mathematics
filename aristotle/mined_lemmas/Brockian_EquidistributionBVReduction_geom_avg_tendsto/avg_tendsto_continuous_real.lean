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

theorem avg_tendsto_continuous_real {α : ℝ} (hα : Irrational α) (F : AddCircle (1:ℝ) → ℝ)
    (hF : Continuous F) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, F ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℝ)) atTop
      (𝓝 (∫ t : AddCircle (1:ℝ), F t)) := by
  set G : C(AddCircle (1:ℝ), ℂ) := ⟨fun t => (F t : ℂ), Complex.continuous_ofReal.comp hF⟩ with hG
  have h := avg_tendsto_continuous hα G
  have hint : (∫ t : AddCircle (1:ℝ), G t) = ((∫ t : AddCircle (1:ℝ), F t : ℝ) : ℂ) := by
    simp [hG, integral_complex_ofReal]
  rw [hint] at h
  have h2 : Tendsto
      (fun N : ℕ => (((∑ n ∈ range N, F ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℝ) : ℝ) : ℂ))
      atTop (𝓝 (((∫ t : AddCircle (1:ℝ), F t : ℝ) : ℂ))) := by
    refine h.congr (fun N => ?_)
    push_cast [hG]
    rfl
  exact tendsto_ofReal_iff.mp h2

/-! ### Step 3: from continuous functions to intervals -/

/-- A trapezoidal bump: it equals `1` on the closed ball of radius `s` around `c`,
vanishes outside the ball of radius `s + δ`, and takes values in `[0,1]`. -/
