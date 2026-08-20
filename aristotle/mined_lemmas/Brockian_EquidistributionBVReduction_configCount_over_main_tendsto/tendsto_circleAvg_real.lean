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

theorem tendsto_circleAvg_real (halpha : Irrational alpha) (f : C(AddCircle (1 : ℝ), ℝ)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f ((n * alpha : ℝ) : AddCircle (1 : ℝ))) / N)
      atTop (𝓝 (∫ y, f y)) := by
  set F : C(AddCircle (1 : ℝ), ℂ) :=
    (⟨Complex.ofReal, Complex.continuous_ofReal⟩ : C(ℝ, ℂ)).comp f with hFdef
  have hFC : Tendsto (circleAvg alpha F) atTop (𝓝 (∫ y, F y)) := tendsto_circleAvg alpha halpha F
  have hint : (∫ y, F y) = ((∫ y, f y : ℝ) : ℂ) := by
    simp only [hFdef, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
    exact integral_ofReal
  have havg : ∀ N : ℕ, circleAvg alpha F N =
      (((∑ n ∈ Finset.range N, f ((n * alpha : ℝ) : AddCircle (1 : ℝ))) / N : ℝ) : ℂ) := by
    intro N
    simp [circleAvg, hFdef]
  rw [hint] at hFC
  have := (Complex.continuous_re.tendsto _).comp hFC
  simp only [Function.comp_def, havg, Complex.ofReal_re] at this
  exact this

end Weyl

section Bump

/-- A continuous trapezoidal bump on the circle: it equals `1` on the closed ball of radius
`r - d` around `m`, vanishes outside the closed ball of radius `r`, and takes values in `[0, 1]`. -/
