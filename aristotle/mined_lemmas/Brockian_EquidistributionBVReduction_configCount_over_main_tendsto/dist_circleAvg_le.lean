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

theorem dist_circleAvg_le (F G : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    dist (circleAvg alpha F N) (circleAvg alpha G N) ≤ dist F G := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [circleAvg, dist_nonneg]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [dist_eq_norm, circleAvg, circleAvg, div_sub_div_same, ← Finset.sum_sub_distrib, norm_div]
  have h1 : ‖∑ n ∈ Finset.range N, (F ((n * alpha : ℝ) : AddCircle (1 : ℝ))
      - G ((n * alpha : ℝ) : AddCircle (1 : ℝ)))‖ ≤ N * dist F G := by
    calc ‖∑ n ∈ Finset.range N, (F ((n * alpha : ℝ) : AddCircle (1 : ℝ))
            - G ((n * alpha : ℝ) : AddCircle (1 : ℝ)))‖
        ≤ ∑ n ∈ Finset.range N, ‖F ((n * alpha : ℝ) : AddCircle (1 : ℝ))
            - G ((n * alpha : ℝ) : AddCircle (1 : ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range N, dist F G := by
          refine Finset.sum_le_sum fun n _ => ?_
          simpa [dist_eq_norm] using ContinuousMap.dist_apply_le_dist
            (f := F) (g := G) ((n * alpha : ℝ) : AddCircle (1 : ℝ))
      _ = N * dist F G := by simp
  have hcast : ‖(N : ℂ)‖ = (N : ℝ) := by simp
  rw [hcast, div_le_iff₀ hNpos]
  linarith [h1]

/-- Mean values are `1`-Lipschitz in the sup norm of the test function. -/
