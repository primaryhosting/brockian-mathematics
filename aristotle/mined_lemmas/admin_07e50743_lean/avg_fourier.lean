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

lemma avg_fourier (hweyl : ∀ h : ℤ, h ≠ 0 → Tendsto (weylSum u h) atTop (𝓝 0)) (n : ℤ) :
    Tendsto (avg u (fourier n)) atTop (𝓝 (∫ z : UnitAddCircle, fourier n z)) := by
  rw [integral_fourier]
  by_cases hn : n = 0
  · subst hn
    rw [if_pos rfl]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    simp only [avg, fourier_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [inv_mul_cancel₀ hN']
  · simp only [hn, if_false]
    have hrw : avg u (fourier n) = weylSum u n := by
      funext N
      simp only [avg, weylSum, fourier_coe_apply]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring_nf
    rw [hrw]
    exact hweyl n hn

