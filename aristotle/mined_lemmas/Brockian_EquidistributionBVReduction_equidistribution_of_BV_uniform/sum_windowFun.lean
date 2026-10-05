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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace Brockian.EquidistributionBVReduction

/-- The (right-continuous) step function jumping from `0` to `1` at `c`. -/

theorem sum_windowFun {a b : ℝ} (hab : a ≤ b) (x : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, windowFun a b (Int.fract (x n))) =
      (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) := by
  simp only [windowFun_eq_indicator hab]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp

/-- **Equidistribution from convergence of bounded-variation averages.**

If the averages `(1/N) ∑_{n < N} f (frac (x n))` converge to `∫₀¹ f` for every integrable
function `f` of bounded variation on `[0, 1]`, then the sequence `x` is equidistributed mod one
with respect to the uniform measure.  The proof applies the hypothesis to the indicator function
of a window `[a, b)`, whose bounded variation and integrability are established here rather than
assumed, so the statement carries no auxiliary named hypothesis. -/
