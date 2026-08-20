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

/-
Weyl's criterion for equidistribution modulo one, and its application to the
sequence `n ↦ n • α` for irrational `α`.
-/
import Mathlib

open Filter MeasureTheory Metric Set Submodule
open scoped Topology Real

namespace Brockian.Equidistribution

noncomputable section

/-! ## Definitions -/

/-- A sequence `u : ℕ → ℝ` is *equidistributed modulo one* if for every subinterval
`[a, b) ⊆ [0, 1]` the proportion of the first `N` terms whose fractional part lies in `[a, b)`
tends to `b - a`. -/

lemma avgReal_continuous (hweyl : ∀ h : ℤ, h ≠ 0 → Tendsto (weylSum u h) atTop (𝓝 0))
    (f : C(UnitAddCircle, ℝ)) :
    Tendsto (avgReal u f) atTop (𝓝 (∫ z : UnitAddCircle, f z)) := by
  set F : C(UnitAddCircle, ℂ) :=
    ⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp (map_continuous f)⟩ with hF
  have h1 : avg u ⇑F = fun N => ((avgReal u f N : ℝ) : ℂ) := by
    funext N
    simp only [avg, avgReal, hF, ContinuousMap.coe_mk]
    push_cast
    ring
  have h2 : (∫ z : UnitAddCircle, F z) = ((∫ z : UnitAddCircle, f z : ℝ) : ℂ) := by
    simp only [hF, ContinuousMap.coe_mk]
    exact integral_ofReal
  have h3 := avg_continuous u hweyl F
  rw [h2, h1] at h3
  exact tendsto_ofReal_iff.1 h3

/-! ## Continuous approximations of arc indicators -/

/-- The continuous "ramp" on the circle which equals `1` on the closed ball of radius `s - δ`
around `p`, vanishes outside the ball of radius `s`, and interpolates linearly in between. -/
