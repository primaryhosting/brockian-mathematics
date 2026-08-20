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
# Equidistribution of irrational rotations and the BV reduction of configuration counts

This file proves, unconditionally, that for an irrational `α` the number of `n < N` with
`Int.fract (n * α)` in a window `[a, b) ⊆ [0, 1]` is asymptotic to the main term `(b - a) * N`.

The equidistribution input (Weyl's theorem for the sequence `n ↦ n α mod 1`) is proved here from
scratch, via Weyl's criterion: the set of continuous test functions on the circle for which the
Birkhoff averages converge to the mean is a closed submodule containing all characters, hence is
everything, by density of trigonometric polynomials.  A bounded-variation ("BV") style sandwich by
continuous trapezoidal functions then transfers the statement to indicator functions of windows.
-/

open MeasureTheory Filter Set Metric Topology Complex
open scoped BigOperators

namespace Brockian.EquidistributionBVReduction

noncomputable section

/-- The number of `n < N` for which the fractional part of `n * α` lies in the window `[a, b)`. -/

theorem integral_bump_le (m r d : ℝ) (hd : 0 < d) (hr : 0 ≤ r) :
    ∫ y, bump m r d y ≤ 2 * r := by
  have hle : ∀ y, bump m r d y ≤
      (closedBall ((m : ℝ) : AddCircle (1 : ℝ)) r).indicator (fun _ => (1 : ℝ)) y := by
    intro y
    by_cases hy : y ∈ closedBall ((m : ℝ) : AddCircle (1 : ℝ)) r
    · rw [Set.indicator_of_mem hy]
      exact bump_le_one m r d y
    · rw [Set.indicator_of_notMem hy]
      exact le_of_eq (bump_eq_zero hd (le_of_lt (by simpa [mem_closedBall] using hy)))
  have hint := integral_mono (integrable_bump m r d)
    ((integrable_const (1 : ℝ)).indicator measurableSet_closedBall) hle
  rw [integral_indicator_const (1 : ℝ) measurableSet_closedBall, measureReal_def,
    AddCircle.volume_closedBall, ENNReal.toReal_ofReal (le_min zero_le_one (by linarith))] at hint
  simp only [smul_eq_mul, mul_one] at hint
  exact le_trans hint (min_le_right _ _)

