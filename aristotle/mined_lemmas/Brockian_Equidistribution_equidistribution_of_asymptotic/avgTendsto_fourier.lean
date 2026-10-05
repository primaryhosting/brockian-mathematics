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

lemma avgTendsto_fourier (x : ℕ → ℝ) (hw : WeylSums x) (k : ℤ) : AvgTendsto x (fourier k) := by
  unfold AvgTendsto
  rw [integral_fourier_eq]
  rcases eq_or_ne k 0 with rfl | hk
  · simp only []
    apply Tendsto.congr' (f₁ := fun _ : ℕ => (1 : ℂ))
    · filter_upwards [eventually_gt_atTop 0] with N hN
      simp [pts, Nat.cast_ne_zero.mpr hN.ne']
    · exact tendsto_const_nhds
  · rw [if_neg hk]
    refine (hw k hk).congr fun N => ?_
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [pts, fourier_coe_apply]
    norm_num

