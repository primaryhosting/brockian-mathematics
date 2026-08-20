import Brockian.Equidistribution

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
# Weyl equidistribution

This file develops, from scratch, Weyl's criterion for equidistribution modulo one and applies
it to the sequence `n ↦ n * α` for irrational `α`.

The main statement is `Brockian.Equidistribution.equidistribution_of_asymptotic_exists`, which
is *conditional* on the asymptotic vanishing of the Weyl exponential sums, and its unconditional
consequence `Brockian.Equidistribution.equidistributedMod1_natMul_irrational`.
-/

namespace Brockian.Equidistribution

open MeasureTheory Filter Finset Complex Topology Metric

open scoped Real

noncomputable section

/-- The number of indices `n < N` for which the fractional part of `x n` lies in `[a, b)`. -/

theorem equidistributedMod1_of_weylCondition (x : ℕ → ℝ) (hx : WeylCondition x) :
    EquidistributedMod1 x := by
  intro a b ha hab hb
  rcases eq_or_lt_of_le (show b - a ≤ 1 by linarith) with hfull | hlt
  · have ha0 : a = 0 := by linarith
    have hb1 : b = 1 := by linarith
    subst ha0; subst hb1
    rw [show (1 : ℝ) - 0 = 1 by norm_num]
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℝ)))
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hcnt : countIn x 0 1 N = N := by
      rw [countIn, Finset.filter_true_of_mem, Finset.card_range]
      intro n _
      exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    rw [hcnt, div_self (by positivity)]
  · rw [Metric.tendsto_atTop]
    intro δ hδ
    set r := (b - a) / 2 with hr
    set c := (a + b) / 2 with hc
    have hr0 : 0 ≤ r := by rw [hr]; linarith
    have hrhalf : r < 1 / 2 := by rw [hr]; linarith
    set ep := min (δ / 8) ((1 / 2 - r) / 2) with hep_def
    have hep : 0 < ep := lt_min (by linarith) (by linarith)
    have hep1 : ep ≤ δ / 8 := min_le_left _ _
    have hep2 : r + ep ≤ 1 / 2 := by
      have := min_le_right (δ / 8) ((1 / 2 - r) / 2)
      rw [← hep_def] at this
      linarith
    have hlow := ravg_tendsto_integral x hx (bump c r ep)
    have hup := ravg_tendsto_integral x hx (bump c (r + ep) ep)
    have hI1 : 2 * (r - ep) ≤ ∫ z, bump c r ep z := le_integral_bump c r ep hep (by linarith)
    have hI2 : (∫ z, bump c (r + ep) ep z) ≤ 2 * (r + ep) :=
      integral_bump_le c (r + ep) ep hep (by linarith) hep2
    rw [Metric.tendsto_atTop] at hlow hup
    obtain ⟨M1, hM1⟩ := hlow (δ / 4) (by linarith)
    obtain ⟨M2, hM2⟩ := hup (δ / 4) (by linarith)
    refine ⟨max M1 M2, fun N hN => ?_⟩
    have e1 := hM1 N (le_trans (le_max_left _ _) hN)
    have e2 := hM2 N (le_trans (le_max_right _ _) hN)
    rw [Real.dist_eq, abs_lt] at e1 e2 ⊢
    have s1 := ravg_bump_le_count x a b ha hb ep hep N
    have s2 := count_le_ravg_bump x a b ha hb ep hep N
    rw [← hc, ← hr] at s1 s2
    exact ⟨by linarith [e1.1, s1], by linarith [e2.2, s2]⟩

/-! ### The exponential sums for `n * α` -/

