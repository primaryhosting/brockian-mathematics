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

lemma integral_le_measureReal {A : Set UnitAddCircle} (hA : MeasurableSet A)
    (g : C(UnitAddCircle, ℝ)) (hg : ∀ z, g z ≤ A.indicator 1 z) :
    ∫ z : UnitAddCircle, g z ≤ volume.real A := by
  have hint : Integrable (A.indicator (1 : UnitAddCircle → ℝ)) volume :=
    (integrable_indicator_iff hA).2 (integrableOn_const (by simp [measure_ne_top]))
  have := integral_mono (integrable_of_continuous_real g) hint hg
  rwa [integral_indicator_one hA] at this

