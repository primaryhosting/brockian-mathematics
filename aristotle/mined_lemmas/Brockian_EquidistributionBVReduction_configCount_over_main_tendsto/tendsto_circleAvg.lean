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

theorem tendsto_circleAvg (halpha : Irrational alpha) (F : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (circleAvg alpha F) atTop (𝓝 (∫ y, F y)) := by
  have hspan : Submodule.span ℂ (Set.range (fourier : ℤ → C(AddCircle (1 : ℝ), ℂ)))
      ≤ weylGood alpha := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact fourier_mem_weylGood alpha halpha k
  have hall := Submodule.topologicalClosure_minimal _ hspan (isClosed_weylGood alpha)
  rw [span_fourier_closure_eq_top] at hall
  exact hall (Submodule.mem_top)

/-- Weyl's equidistribution theorem for continuous real test functions. -/
