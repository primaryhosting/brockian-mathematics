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

lemma fract_eq_fract_of_coe_eq {x y : ℝ} (h : (x : UnitAddCircle) = (y : UnitAddCircle)) :
    Int.fract x = Int.fract y := by
  have h2 : Int.fract x ∈ Ico (0 : ℝ) (0 + 1) :=
    mem_Ico.2 ⟨Int.fract_nonneg x, by simpa using Int.fract_lt_one x⟩
  have h3 : Int.fract y ∈ Ico (0 : ℝ) (0 + 1) :=
    mem_Ico.2 ⟨Int.fract_nonneg y, by simpa using Int.fract_lt_one y⟩
  rw [← AddCircle.coe_eq_coe_iff_of_mem_Ico h2 h3, coe_fract, coe_fract]
  exact h

