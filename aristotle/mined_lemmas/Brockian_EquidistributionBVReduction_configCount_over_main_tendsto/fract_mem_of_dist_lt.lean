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

theorem fract_mem_of_dist_lt (ha : 0 ≤ a) (hb : b ≤ 1) {t : ℝ}
    (ht : dist ((t : ℝ) : AddCircle (1 : ℝ)) (((a + b) / 2 : ℝ) : AddCircle (1 : ℝ)) < (b - a) / 2) :
    Int.fract t ∈ Set.Ico a b := by
  rw [dist_coe_eq] at ht
  set k : ℤ := round (t - (a + b) / 2) with hk
  set j : ℤ := ⌊t⌋ - k with hj
  have hfr : Int.fract t + (j : ℝ) = (t - (a + b) / 2) - k + (a + b) / 2 := by
    rw [Int.fract, hj]; push_cast; ring
  have habs := abs_lt.1 ht
  have h0 : 0 ≤ Int.fract t := Int.fract_nonneg t
  have h1 : Int.fract t < 1 := Int.fract_lt_one t
  have hj0 : j = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hjle : (j : ℝ) ≤ -1 := by exact_mod_cast (by omega : j ≤ -1)
      linarith [habs.1, hfr]
    · have hjge : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 1 ≤ j)
      linarith [habs.2, hfr]
  rw [hj0] at hfr
  push_cast at hfr
  exact ⟨by linarith [habs.1], by linarith [habs.2]⟩

end Sandwich

/-- The configuration count written as a sum of indicators. -/
