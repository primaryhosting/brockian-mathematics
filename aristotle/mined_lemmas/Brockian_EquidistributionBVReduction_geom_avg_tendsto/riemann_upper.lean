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
# Equidistribution of irrational rotations and the bounded-variation reduction

This file develops, from scratch, Weyl's equidistribution theorem for the sequence
`n ↦ n • α mod 1` (`α` irrational) and reduces averages of functions of bounded variation
to their integral.

The final result `total_over_main_tendsto` states that, for a function `f` of bounded
variation on `[0,1]` with nonzero integral, the *total*
`∑_{n < N} f (fract (n α))` divided by the *main term* `N * ∫₀¹ f` tends to `1`.
-/

open Filter Finset Set MeasureTheory Metric
open scoped Topology

namespace Brockian.EquidistributionBVReduction

noncomputable section

/-- A sequence of reals is equidistributed mod one when, for every subinterval `[a,b) ⊆ [0,1]`,
the proportion of the first `N` fractional parts lying in `[a, b)` tends to `b - a`. -/

theorem riemann_upper {f : ℝ → ℝ} (hf : MonotoneOn f (Icc 0 1)) {m : ℕ} (hm : 0 < m) :
    (∫ t in (0:ℝ)..1, f t) ≤ ∑ i ∈ range m, f (((i:ℝ)+1)/m) / m := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  set a : ℕ → ℝ := fun i => (i:ℝ)/m with ha
  have hsub : ∀ i ≤ m, a i ∈ Icc (0:ℝ) 1 := by
    intro i hi
    refine ⟨by positivity, ?_⟩
    rw [ha]; simp only; rw [div_le_one hmpos]; exact_mod_cast hi
  have hmono : ∀ i < m, MonotoneOn f (uIcc (a i) (a (i+1))) := by
    intro i hi
    refine hf.mono ?_
    rw [Set.uIcc_of_le (by rw [ha]; simp only; gcongr; simp)]
    intro y hy
    exact ⟨le_trans (hsub i (le_of_lt hi)).1 hy.1, le_trans hy.2 (hsub (i+1) hi).2⟩
  have hint : ∀ i < m, IntervalIntegrable f volume (a i) (a (i+1)) :=
    fun i hi => (hmono i hi).intervalIntegrable
  have hsplit : ∑ i ∈ range m, ∫ t in (a i)..(a (i+1)), f t = ∫ t in (a 0)..(a m), f t :=
    intervalIntegral.sum_integral_adjacent_intervals hint
  have ha0 : a 0 = 0 := by simp [ha]
  have ham : a m = 1 := by rw [ha]; field_simp
  rw [ha0, ham] at hsplit
  rw [← hsplit]
  refine sum_le_sum fun i hi => ?_
  have hi' : i < m := mem_range.1 hi
  have hle : a i ≤ a (i+1) := by rw [ha]; simp only; gcongr; simp
  have hcomp : ∫ t in (a i)..(a (i+1)), f t ≤ ∫ _t in (a i)..(a (i+1)), f (a (i+1)) := by
    refine intervalIntegral.integral_mono_on hle (hint i hi') (_root_.intervalIntegrable_const) ?_
    intro y hy
    exact hf ⟨le_trans (hsub i hi'.le).1 hy.1, le_trans hy.2 (hsub (i+1) hi').2⟩
      (hsub (i+1) hi') hy.2
  rw [intervalIntegral.integral_const, smul_eq_mul] at hcomp
  have hlen : a (i+1) - a i = 1/m := by rw [ha]; push_cast; field_simp; ring
  rw [hlen] at hcomp
  calc ∫ t in (a i)..(a (i+1)), f t ≤  1/m * f (a (i+1)) := hcomp
    _ = f (((i:ℝ)+1)/m)/m := by rw [ha]; push_cast; ring

/-- The difference between the upper and the lower Riemann sums is `(f 1 - f 0)/m`. -/
