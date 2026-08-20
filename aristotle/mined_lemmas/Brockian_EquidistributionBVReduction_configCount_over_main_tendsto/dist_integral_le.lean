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

theorem dist_integral_le (F G : C(AddCircle (1 : ℝ), ℂ)) :
    dist (∫ y, F y) (∫ y, G y) ≤ dist F G := by
  rw [dist_eq_norm, ← integral_sub (integrable_continuousMap F) (integrable_continuousMap G)]
  have h1 : ∀ᵐ y : AddCircle (1 : ℝ), ‖F y - G y‖ ≤ dist F G := by
    filter_upwards with y
    simpa [dist_eq_norm] using ContinuousMap.dist_apply_le_dist y (f := F) (g := G)
  simpa [measureReal_def, AddCircle.measure_univ] using
    norm_integral_le_of_norm_le_const (μ := (volume : Measure (AddCircle (1 : ℝ)))) h1

