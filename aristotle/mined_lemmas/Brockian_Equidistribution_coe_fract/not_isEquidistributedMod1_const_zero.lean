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

theorem not_isEquidistributedMod1_const_zero : ¬ IsEquidistributedMod1 (fun _ : ℕ => (0 : ℝ)) := by
  intro h
  have h2 := h 0 (1 / 2) le_rfl (by norm_num) (by norm_num)
  have heq : ∀ N : ℕ, (((Finset.range N).filter
      fun k => Int.fract ((fun _ : ℕ => (0 : ℝ)) k) ∈ Ico (0 : ℝ) (1 / 2)).card : ℝ) / N
      = (N : ℝ) / N := by
    intro N
    congr 2
    rw [Finset.filter_true_of_mem]
    · simp
    · intro k _
      simp [Int.fract]
  rw [show (fun N : ℕ => (((Finset.range N).filter
      fun k => Int.fract ((fun _ : ℕ => (0 : ℝ)) k) ∈ Ico (0 : ℝ) (1 / 2)).card : ℝ) / N)
      = fun N : ℕ => (N : ℝ) / N from funext heq] at h2
  have h3 : Tendsto (fun N : ℕ => (N : ℝ) / N) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    field_simp
  have h4 := tendsto_nhds_unique h2 h3
  norm_num at h4

/-- **Weyl's equidistribution theorem**: for irrational `α`, the sequence `n ↦ n α`
is equidistributed modulo one. -/
