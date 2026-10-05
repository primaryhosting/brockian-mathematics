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
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.Brockian.BetrothedNumbers.Basic

/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Elementary analytic input: numbers of large abundancy are rare

This file proves, unconditionally, the analytic-number-theory ingredients of the
reduction:

* `Brockian.BetrothedNumbers.sum_divisors_swap`: Dirichlet's hyperbola-style
  interchange `∑_{n ≤ x} ∑_{d ∣ n} f d = ∑_{d ≤ x} ⌊x/d⌋ f d`;
* `Brockian.BetrothedNumbers.sum_sigma_div_self_le`: the mean value bound
  `∑_{n ≤ x} σ(n)/n ≤ 2x`;
* `Brockian.BetrothedNumbers.abundant_count_le`: the Markov/Chebyshev bound
  `#{n ≤ x : σ(n) > K n} ≤ 2x/K`;
* `Brockian.BetrothedNumbers.hasDensityZero_of_forall_le`: a convenient
  criterion for asymptotic density zero.
-/

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction Finset

/-- The set of integers of abundancy larger than `K`, i.e. `σ(n) > K n`. -/

theorem sum_inv_sq_le (x : ℕ) :
    ∑ d ∈ Finset.Ioc 0 x, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 2 - 1 / (max x 1 : ℕ) := by
  induction x with
  | zero => norm_num
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · norm_num
      · rw [Finset.sum_Ioc_succ_top (by omega)]
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have h1 : ((max n 1 : ℕ) : ℝ) = (n : ℝ) := by simp [Nat.max_eq_left hn]
        have h2 : ((max (n + 1) 1 : ℕ) : ℝ) = ((n : ℝ) + 1) := by simp
        rw [h1] at ih
        rw [h2]
        have key : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
          rw [div_sub_div _ _ (by linarith) (by linarith),
            div_le_div_iff₀ (by positivity) (by positivity)]
          ring_nf
          nlinarith
        push_cast
        linarith

/-- Mean value bound for the abundancy: `∑_{0 < n ≤ x} σ(n)/n ≤ 2x`. -/
