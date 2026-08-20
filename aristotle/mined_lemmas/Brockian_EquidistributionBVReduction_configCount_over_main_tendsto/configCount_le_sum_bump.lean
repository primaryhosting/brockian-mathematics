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

theorem configCount_le_sum_bump {alpha a b : ℝ} (d : ℝ) (hd : 0 < d) (N : ℕ) :
    (configCount alpha a b N : ℝ) ≤ ∑ n ∈ Finset.range N,
      bump ((a + b) / 2) ((b - a) / 2 + d) d ((n * alpha : ℝ) : AddCircle (1 : ℝ)) := by
  rw [configCount_eq_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  by_cases hmem : Int.fract ((n : ℝ) * alpha) ∈ Set.Ico a b
  · rw [if_pos hmem]
    exact le_of_eq (bump_eq_one hd (by simpa using dist_le_of_fract_mem hmem)).symm
  · rw [if_neg hmem]
    exact bump_nonneg _ _ _ _

/-- The count is bounded below by a Birkhoff sum of a bump supported in the window. -/
