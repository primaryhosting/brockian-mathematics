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

lemma integral_arcUpper_le (c : AddCircle (1 : ℝ)) (r ε : ℝ) (hε : 0 < ε) (hr : 0 ≤ r) :
    (∫ t : AddCircle (1 : ℝ), arcUpper c r ε t) ≤ 2 * r + 2 * ε := by
  have hle : ∀ t, arcUpper c r ε t ≤ (closedBall c (r + ε)).indicator (fun _ => (1 : ℝ)) t := by
    intro t
    by_cases ht : t ∈ closedBall c (r + ε)
    · rw [indicator_of_mem ht]; exact min_le_left _ _
    · rw [indicator_of_notMem ht]
      simp only [mem_closedBall, not_le] at ht
      have hz : (r + ε - dist t c) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
      simp [arcUpper, max_eq_left hz]
  have hint : (∫ t : AddCircle (1 : ℝ), arcUpper c r ε t)
      ≤ ∫ t : AddCircle (1 : ℝ), (closedBall c (r + ε)).indicator (fun _ => (1 : ℝ)) t :=
    integral_mono ((continuous_arcUpper c r ε).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
      ((integrable_const (1 : ℝ)).indicator measurableSet_closedBall) hle
  refine hint.trans ?_
  rw [integral_indicator_const (1 : ℝ) measurableSet_closedBall, smul_eq_mul, mul_one,
    measureReal_def, AddCircle.volume_closedBall, ENNReal.toReal_ofReal (by positivity)]
  exact (min_le_right _ _).trans (by linarith)

