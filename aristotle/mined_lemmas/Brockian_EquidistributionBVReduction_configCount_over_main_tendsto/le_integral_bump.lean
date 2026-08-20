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

theorem le_integral_bump (m r d : ℝ) (hd : 0 < d) (hr : r ≤ 1 / 2) :
    2 * (r - d) ≤ ∫ y, bump m r d y := by
  rcases lt_or_ge (r - d) 0 with h | h
  · have hpos : (0 : ℝ) ≤ ∫ y, bump m r d y := integral_nonneg fun y => bump_nonneg m r d y
    linarith
  · have hle : ∀ y, (closedBall ((m : ℝ) : AddCircle (1 : ℝ)) (r - d)).indicator
        (fun _ => (1 : ℝ)) y ≤ bump m r d y := by
      intro y
      by_cases hy : y ∈ closedBall ((m : ℝ) : AddCircle (1 : ℝ)) (r - d)
      · rw [Set.indicator_of_mem hy]
        exact le_of_eq (bump_eq_one hd (by simpa [mem_closedBall] using hy)).symm
      · rw [Set.indicator_of_notMem hy]
        exact bump_nonneg m r d y
    have hint := integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_closedBall)
      (integrable_bump m r d) hle
    rw [integral_indicator_const (1 : ℝ) measurableSet_closedBall, measureReal_def,
      AddCircle.volume_closedBall, ENNReal.toReal_ofReal (le_min zero_le_one (by linarith)),
      min_eq_right (by linarith)] at hint
    simpa using hint

end Bump

section Sandwich

variable {alpha a b : ℝ}

/-- The circle distance between the classes of two reals, computed on representatives. -/
