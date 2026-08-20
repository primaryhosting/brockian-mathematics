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

theorem avg_fourier_tendsto {α : ℝ} (hα : Irrational α) (k : ℤ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, fourier k ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ))
      atTop (𝓝 (∫ t : AddCircle (1:ℝ), fourier k t)) := by
  rw [integral_fourier]
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl]
    have : ∀ N : ℕ, N ≠ 0 →
        (∑ n ∈ range N, fourier (0:ℤ) ((n * α : ℝ) : AddCircle (1:ℝ))) / (N:ℂ) = 1 := by
      intro N hN
      simp only [fourier_zero, sum_const, card_range, nsmul_eq_mul, mul_one]
      exact div_self (Nat.cast_ne_zero.mpr hN)
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ne_atTop 0] with N hN using (this N hN).symm
  · simp only [if_neg hk]
    have hz : ‖fourier k ((α : ℝ) : AddCircle (1:ℝ))‖ = 1 := norm_fourier_coe k α
    have := geom_avg_tendsto _ hz (fourier_ne_one hα hk)
    refine this.congr (fun N => ?_)
    congr 1
    exact (sum_congr rfl fun n _ => (fourier_orbit α k n)).symm

/-! ### Step 2: from characters to all continuous functions -/

/-- The averaging result for trigonometric polynomials. -/
