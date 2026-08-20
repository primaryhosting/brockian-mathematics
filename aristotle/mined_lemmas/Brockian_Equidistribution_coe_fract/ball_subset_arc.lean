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

lemma ball_subset_arc (a b : ℝ) :
    ball (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2) ⊆ arc a b := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := exists_repr ((a + b) / 2) z
  rw [mem_ball, dist_coe_coe] at hz
  have heq : ‖((x - (a + b) / 2 : ℝ) : UnitAddCircle)‖ = |x - (a + b) / 2| := by
    rw [AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero]
    simpa using hx
  rw [heq, abs_lt] at hz
  exact ⟨x, mem_Ico.2 ⟨by linarith [hz.1], by linarith [hz.2]⟩, rfl⟩

/-! ## Averages of continuous functions -/

