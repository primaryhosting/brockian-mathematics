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

theorem count_le_ravg_bump (x : ℕ → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (ep : ℝ)
    (hep : 0 < ep) (N : ℕ) :
    (countIn x a b N : ℝ) / N ≤ ravg x (bump ((a + b) / 2) ((b - a) / 2 + ep) ep) N := by
  have hdiv : (countIn x a b N : ℝ) / N
      = (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
          (if Int.fract (x n) ∈ Set.Ico a b then (1 : ℝ) else 0) := by
    rw [countIn_eq_sum, div_eq_inv_mul]
  rw [hdiv, ravg]
  have hNn : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => ?_) hNn
  by_cases hmem : Int.fract (x n) ∈ Set.Ico a b
  · rw [if_pos hmem, bump_eq_one _ _ _ hep (by simpa using norm_le_of_fract_mem ha hb hmem)]
  · rw [if_neg hmem]
    exact bump_nonneg _ _ _ _

/-- **Weyl's criterion.** A sequence whose nontrivial exponential sums have vanishing averages is
equidistributed modulo one. -/
