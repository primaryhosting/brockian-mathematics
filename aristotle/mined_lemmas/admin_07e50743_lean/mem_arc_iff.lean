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

lemma mem_arc_iff {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (x : ℝ) :
    (x : UnitAddCircle) ∈ arc a b ↔ Int.fract x ∈ Ico a b := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hy1 : Int.fract y = y := Int.fract_eq_self.2 ⟨le_trans ha hy.1, lt_of_lt_of_le hy.2 hb⟩
    have h2 := fract_eq_fract_of_coe_eq hyx
    rw [hy1] at h2
    rwa [h2] at hy
  · intro hx
    exact ⟨Int.fract x, hx, coe_fract x⟩

