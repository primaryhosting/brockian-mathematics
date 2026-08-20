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

lemma rampAt_eq_zero {p : UnitAddCircle} {s δ : ℝ} (hδ : 0 < δ) {z : UnitAddCircle}
    (h : s ≤ dist z p) : rampAt p s δ z = 0 := by
  have h1 : (s - dist z p) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  simp only [rampAt, ContinuousMap.coe_mk]
  rw [max_eq_left h1, min_eq_right zero_le_one]

