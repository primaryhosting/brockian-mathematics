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
# Equidistribution: reduction from continuous test functions to BV (indicator) test functions

This file contains the classical "bounded variation reduction" step in the theory of
equidistribution modulo one: if a sequence `x : ℕ → ℝ` is equidistributed mod `1` in Weyl's
sense (Cesàro averages of *continuous* `1`-periodic test functions converge to the mean of the
test function), then the counting density of the "configurations" `n ↦ Int.fract (x n)` lying in
a subinterval `[a, b) ⊆ [0, 1)` converges to the length `b - a`.

The indicator of an interval is the basic example of a function of bounded variation which is not
continuous, so the content of the main theorem is exactly that the class of admissible test
functions may be enlarged from continuous functions to such BV functions.

The main result is `Brockian.EquidistributionBVReduction.configCount_density_of_BV`; it is
unconditional apart from the (necessary) equidistribution hypothesis on the sequence itself.
-/

open Filter Set MeasureTheory
open scoped Topology BigOperators Classical

namespace Brockian.EquidistributionBVReduction

/-- The number of indices `n < N` whose fractional part `Int.fract (x n)` lies in `[a, b)`. -/

lemma configCount_eventually_ge {x : ℕ → ℝ} (hx : EquidistributedMod1 x) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (b - a) - ε ≤ (configCount x a b N : ℝ) / N := by
  rcases le_or_gt (b - a) ε with hcase | hcase
  · filter_upwards with N
    have : (0:ℝ) ≤ (configCount x a b N : ℝ) / N :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith
  · set d : ℝ := ε / 4 with hd_def
    have hd : 0 < d := by positivity
    have hmid : a + d ≤ b - d := by simp only [hd_def]; linarith
    set g : ℝ → ℝ := trap a b d with hg_def
    have hg0 : g 0 = g 1 := by
      rw [hg_def, trap_eq_zero_of_le hd ha, trap_eq_zero_of_ge hd hb]
    have hgc : Continuous g := trap_continuous a b d
    set G : ℝ → ℝ := periodize g with hG_def
    have hGc : Continuous G := periodize_continuous hg0 hgc.continuousOn
    have hGp : Function.Periodic G 1 := periodize_periodic g
    have hGint : (∫ t in (0:ℝ)..1, G t) = ∫ t in (0:ℝ)..1, g t := by
      refine intervalIntegral.integral_congr ?_
      rw [Set.uIcc_of_le (zero_le_one)]
      exact periodize_eqOn g hg0
    have hlow : b - a - ε / 2 ≤ ∫ t in (0:ℝ)..1, G t := by
      rw [hGint]
      have h := trap_integral_lower hd ha hb hmid
      simp only [hd_def] at h ⊢
      linarith
    have htend := hx G hGc hGp
    have hgt : (b - a) - ε < ∫ t in (0:ℝ)..1, G t := by linarith
    have hev := htend.eventually_const_lt hgt
    filter_upwards [hev, eventually_gt_atTop 0] with N hN hN0
    have hNpos : (0:ℝ) < N := by exact_mod_cast hN0
    have hsum : (∑ n ∈ Finset.range N, G (x n)) ≤ (configCount x a b N : ℝ) := by
      rw [configCount_eq_sum]
      exact Finset.sum_le_sum fun n _ => trap_le_indicator hd _
    calc (b - a) - ε ≤ (∑ n ∈ Finset.range N, G (x n)) / N := hN.le
      _ ≤ (configCount x a b N : ℝ) / N := by gcongr

