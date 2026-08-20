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

theorem configCount_div_tendsto {alpha a b : ℝ} (halpha : Irrational alpha) (ha : 0 ≤ a)
    (hab : a < b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (configCount alpha a b N : ℝ) / N) atTop (𝓝 (b - a)) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  set d : ℝ := eps / 4 with hd_def
  have hd : 0 < d := by positivity
  set r : ℝ := (b - a) / 2 with hr_def
  set m : ℝ := (a + b) / 2 with hm_def
  have hrhalf : r ≤ 1 / 2 := by rw [hr_def]; linarith
  have hr0 : 0 < r := by rw [hr_def]; linarith
  have hUint : ∫ y, (bump m (r + d) d) y ≤ 2 * (r + d) :=
    integral_bump_le m (r + d) d hd (by linarith)
  have hLint : 2 * (r - d) ≤ ∫ y, (bump m r d) y := le_integral_bump m r d hd hrhalf
  have hUtend := tendsto_circleAvg_real alpha halpha (bump m (r + d) d)
  have hLtend := tendsto_circleAvg_real alpha halpha (bump m r d)
  rw [Metric.tendsto_atTop] at hUtend hLtend
  obtain ⟨N1, hN1⟩ := hUtend d hd
  obtain ⟨N2, hN2⟩ := hLtend d hd
  refine ⟨max (max N1 N2) 1, fun N hN => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hN)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have h1 := hN1 N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
  have h2 := hN2 N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  rw [Real.dist_eq, abs_lt] at h1 h2 ⊢
  have hup := configCount_le_sum_bump (alpha := alpha) (a := a) (b := b) d hd N
  have hlo := sum_bump_le_configCount (alpha := alpha) (a := a) (b := b) ha hb d hd N
  rw [← hr_def, ← hm_def] at hup hlo
  have hupdiv : (configCount alpha a b N : ℝ) / N
      ≤ (∑ n ∈ Finset.range N, (bump m (r + d) d) ((n * alpha : ℝ) : AddCircle (1 : ℝ))) / N := by
    gcongr
  have hlodiv : (∑ n ∈ Finset.range N, (bump m r d) ((n * alpha : ℝ) : AddCircle (1 : ℝ))) / N
      ≤ (configCount alpha a b N : ℝ) / N := by
    gcongr
  have h2r : 2 * r = b - a := by rw [hr_def]; ring
  constructor
  · linarith [h2.1, hLint, hlodiv]
  · linarith [h1.2, hUint, hupdiv]

/-- **Equidistribution / BV reduction.** For irrational `alpha` and a window `[a, b) ⊆ [0, 1]` of
positive length, the number of `n < N` with `Int.fract (n * alpha) ∈ [a, b)` is asymptotic to the
main term `(b - a) * N`. -/
