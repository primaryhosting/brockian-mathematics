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

theorem mem_Ico_of_dist_lt {a b t : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t < 1)
    (h : dist ((t : ℝ) : AddCircle (1:ℝ)) (((a+b)/2 : ℝ) : AddCircle (1:ℝ)) < (b-a)/2) :
    t ∈ Ico a b := by
  set u : ℝ := t - (a+b)/2 with hu
  have hdist : dist ((t : ℝ) : AddCircle (1:ℝ)) (((a+b)/2 : ℝ) : AddCircle (1:ℝ))
      = |u - (round u : ℝ)| := by
    rw [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq]
    simp [hu]
  rw [hdist] at h
  have habs : a < b := by
    rcases lt_or_eq_of_le hab with h1 | h1
    · exact h1
    · exact absurd h (by rw [← h1]; simp)
  have hr : (b-a)/2 ≤ 1/2 := by linarith
  have hu1 : -1 < u ∧ u < 1 := by constructor <;> simp only [hu] <;> linarith
  have habs' : |u - (round u : ℝ)| < 1/2 := lt_of_lt_of_le h hr
  rw [abs_lt] at habs'
  have hm2 : round u < 2 := by
    exact_mod_cast (show ((round u : ℤ):ℝ) < 2 by linarith [hu1.1, hu1.2])
  have hm2' : -2 < round u := by
    exact_mod_cast (show (-2:ℝ) < ((round u : ℤ):ℝ) by linarith [hu1.1, hu1.2])
  have hmem : round u = -1 ∨ round u = 0 ∨ round u = 1 := by omega
  rcases hmem with h1 | h1 | h1 <;> rw [h1] at h <;> push_cast at h <;> rw [abs_lt] at h <;>
    simp only [hu] at h <;> exact ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩

/-- A convenient criterion for convergence of a real sequence. -/
