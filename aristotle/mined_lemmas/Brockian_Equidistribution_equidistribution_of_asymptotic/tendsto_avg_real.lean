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

lemma tendsto_avg_real (x : ℕ → ℝ) (hw : WeylSums x) (f : AddCircle (1 : ℝ) → ℝ)
    (hf : Continuous f) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ range N, f (pts x n)) atTop
      (𝓝 (∫ t : AddCircle (1 : ℝ), f t)) := by
  have h := avgTendsto_continuous x hw ⟨fun t => (f t : ℂ), Complex.continuous_ofReal.comp hf⟩
  rw [AvgTendsto] at h
  simp only [ContinuousMap.coe_mk, integral_complex_ofReal] at h
  refine ((Complex.continuous_re.tendsto _).comp h).congr fun N => ?_
  simp [Function.comp, ← Complex.ofReal_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    ← Complex.ofReal_mul]

/-! ### Continuous approximations to the indicator of an arc -/

/-- Continuous upper approximation to the indicator function of the closed arc of radius `r`
centred at `c`; it equals `1` on that arc and vanishes outside the arc of radius `r + ε`. -/
