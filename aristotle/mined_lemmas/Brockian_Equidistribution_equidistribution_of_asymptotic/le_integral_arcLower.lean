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
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic

This file proves **Weyl's criterion**: if a real sequence `x` satisfies the asymptotic
exponential-sum estimate `∑_{n < N} e(h * xₙ) = o(N)` for every nonzero integer `h`, then `x`
is equidistributed modulo one, i.e. for every subinterval `[a, b) ⊆ [0, 1)` the proportion of
indices `n < N` with `Int.fract (xₙ) ∈ [a, b)` tends to `b - a`.
-/

open Filter Finset MeasureTheory Metric Set Submodule
open scoped BigOperators Real Topology

namespace Brockian.Equidistribution

noncomputable section

/-- The image of a real sequence in the circle `ℝ / ℤ`. -/

lemma le_integral_arcLower (c : AddCircle (1 : ℝ)) (r ε : ℝ) (hε : 0 < ε) (hr : 2 * (r - ε) ≤ 1) :
    2 * r - 2 * ε ≤ ∫ t : AddCircle (1 : ℝ), arcLower c r ε t := by
  have hle : ∀ t, (closedBall c (r - ε)).indicator (fun _ => (1 : ℝ)) t ≤ arcLower c r ε t := by
    intro t
    by_cases ht : t ∈ closedBall c (r - ε)
    · rw [indicator_of_mem ht]
      simp only [mem_closedBall] at ht
      refine le_min le_rfl (le_max_of_le_right ?_)
      rw [le_div_iff₀ hε]
      linarith
    · rw [indicator_of_notMem ht]
      exact le_min zero_le_one (le_max_left _ _)
  have hint : (∫ t : AddCircle (1 : ℝ), (closedBall c (r - ε)).indicator (fun _ => (1 : ℝ)) t)
      ≤ ∫ t : AddCircle (1 : ℝ), arcLower c r ε t :=
    integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_closedBall)
      ((continuous_arcLower c r ε).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)) hle
  refine le_trans ?_ hint
  rw [integral_indicator_const (1 : ℝ) measurableSet_closedBall, smul_eq_mul, mul_one,
    measureReal_def, AddCircle.volume_closedBall]
  rcases le_or_gt 0 (2 * (r - ε)) with h | h
  · rw [ENNReal.toReal_ofReal (le_min (by norm_num) h), le_min_iff]
    constructor <;> linarith
  · have hzero : ENNReal.ofReal (min (1 : ℝ) (2 * (r - ε))) = 0 := by
      rw [ENNReal.ofReal_eq_zero]
      exact (min_le_right _ _).trans h.le
    rw [hzero]
    simp only [ENNReal.toReal_zero]
    linarith

/-! ### The arc geometry of `[a, b) ⊆ [0, 1)` -/

