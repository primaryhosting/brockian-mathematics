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

import Brockian.WeylEquidistribution

/-!
# Equidistribution: reduction of a configuration count to its main term

Fix an irrational number `a`, a point `c` on the circle `ℝ/ℤ` and a radius `r` with
`0 < r < 1/2`.  Call `n` *admissible* if the orbit point `n • a` lies within distance `r` of `c`
on `ℝ/ℤ`.  `configCount a c r N` counts the admissible `n < N`, and the expected main term is
`mainTerm r N = 2 * r * N` (the measure of the arc times the number of trials).

The main result `configCount_over_main_tendsto` states that the ratio of the count to the main
term tends to `1`.

The analytic input is Weyl's equidistribution theorem for continuous test functions, proved in
`Brockian.WeylEquidistribution`; the passage from continuous test functions to the (bounded
variation, indeed indicator) test function of an arc is done here by sandwiching the indicator
between two explicit continuous, piecewise-linear functions.
-/

open MeasureTheory Filter Topology Metric
open scoped BigOperators

namespace Brockian
namespace EquidistributionBVReduction

open Brockian.Weyl

noncomputable section

open scoped Classical in
/-- The number of `n < N` for which the orbit point `n • a` lies within distance `r` of `c`
on the circle `ℝ/ℤ`. -/

theorem configCount_div_tendsto (a c r : ℝ) (ha : Equidistributed a) (hr : 0 < r)
    (hr2 : r < 1 / 2) :
    Tendsto (fun N : ℕ => (configCount a c r N : ℝ) / N) atTop (𝓝 (2 * r)) := by
  rw [Metric.tendsto_atTop]
  intro e he
  set d : ℝ := min (e / 4) (r / 2) with hd_def
  have hd : 0 < d := lt_min (by linarith) (by linarith)
  have hde : d ≤ e / 4 := min_le_left _ _
  have hdr : d ≤ r / 2 := min_le_right _ _
  have hU := ha (upperFn c r d)
  have hL := ha (lowerFn c r d)
  rw [Metric.tendsto_atTop] at hU hL
  obtain ⟨N₁, hN₁⟩ := hU (e / 4) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hL (e / 4) (by linarith)
  refine ⟨max (max N₁ N₂) 1, fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNpos : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hinv : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  have hUb : (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, upperFn c r d (pt a n)
      < (∫ x : Circ, upperFn c r d x) + e / 4 := by
    have := hN₁ N hN1
    rw [Real.dist_eq, abs_sub_lt_iff] at this
    linarith [this.1]
  have hLb : (∫ x : Circ, lowerFn c r d x) - e / 4
      < (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, lowerFn c r d (pt a n) := by
    have := hN₂ N hN2
    rw [Real.dist_eq, abs_sub_lt_iff] at this
    linarith [this.2]
  have hUi := integral_upperFn_le c r d hd hr
  have hLi := le_integral_lowerFn c r d hd hr2
  have hcu : (N : ℝ)⁻¹ * (configCount a c r N : ℝ)
      ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, upperFn c r d (pt a n) :=
    mul_le_mul_of_nonneg_left (count_le_sum_upper a c r d hd N) hinv
  have hcl : (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, lowerFn c r d (pt a n)
      ≤ (N : ℝ)⁻¹ * (configCount a c r N : ℝ) :=
    mul_le_mul_of_nonneg_left (sum_lower_le_count a c r d hd N) hinv
  rw [Real.dist_eq, abs_sub_lt_iff, div_eq_inv_mul]
  constructor <;> linarith

/-- The reduction of the configuration count to its main term, conditionally on the
equidistribution hypothesis. -/
