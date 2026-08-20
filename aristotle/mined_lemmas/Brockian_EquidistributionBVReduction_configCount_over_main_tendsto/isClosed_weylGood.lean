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

theorem isClosed_weylGood : IsClosed (weylGood alpha : Set C(AddCircle (1 : ℝ), ℂ)) := by
  rw [← closure_subset_iff_isClosed]
  intro F hF
  show Tendsto (circleAvg alpha F) atTop (𝓝 (∫ y, F y))
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨G, hG, hFG⟩ := Metric.mem_closure_iff.1 hF (eps / 3) (by linarith)
  have hGtend : Tendsto (circleAvg alpha G) atTop (𝓝 (∫ y, G y)) := hG
  rw [Metric.tendsto_atTop] at hGtend
  obtain ⟨N₀, hN₀⟩ := hGtend (eps / 3) (by linarith)
  refine ⟨N₀, fun N hN => ?_⟩
  calc dist (circleAvg alpha F N) (∫ y, F y)
      ≤ dist (circleAvg alpha F N) (circleAvg alpha G N)
        + dist (circleAvg alpha G N) (∫ y, G y) + dist (∫ y, G y) (∫ y, F y) := by
        exact dist_triangle4 _ _ _ _
    _ < eps := by
        have h1 := dist_circleAvg_le alpha F G N
        have h2 := hN₀ N hN
        have h3 : dist (∫ y, G y) (∫ y, F y) ≤ dist F G := by
          rw [dist_comm]; exact dist_integral_le F G
        linarith

/-- Weyl's equidistribution theorem for continuous complex test functions. -/
