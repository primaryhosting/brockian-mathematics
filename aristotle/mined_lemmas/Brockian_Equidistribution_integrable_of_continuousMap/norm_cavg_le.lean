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

theorem norm_cavg_le (x : ℕ → ℝ) (f : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    ‖cavg x f N‖ ≤ ‖f‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [cavg, norm_nonneg]
  · rw [cavg, norm_mul, norm_inv]
    have h1 : ‖∑ n ∈ Finset.range N, f (x n)‖ ≤ N * ‖f‖ :=
      calc ‖∑ n ∈ Finset.range N, f (x n)‖ ≤ ∑ n ∈ Finset.range N, ‖f (x n)‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range N, ‖f‖ := Finset.sum_le_sum fun n _ => f.norm_coe_le_norm _
        _ = N * ‖f‖ := by simp
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Complex.norm_natCast, inv_mul_le_iff₀ hNpos]
    exact h1

