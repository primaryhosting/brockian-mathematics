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

theorem sum_sigma_div_self_le (x : ℕ) :
    ∑ n ∈ Finset.Ioc 0 x, (sigma 1 n : ℝ) / n ≤ 2 * x := by
  have h1 : ∑ n ∈ Finset.Ioc 0 x, (sigma 1 n : ℝ) / n
      = ∑ d ∈ Finset.Ioc 0 x, ((x / d : ℕ) : ℝ) * ((1 : ℝ) / d) := by
    rw [← sum_divisors_swap x (fun d => (1 : ℝ) / d)]
    refine Finset.sum_congr rfl ?_
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    exact sigma_div_self n hn.1
  have h2 : ∀ d ∈ Finset.Ioc 0 x, ((x / d : ℕ) : ℝ) * ((1 : ℝ) / d)
      ≤ (x : ℝ) * ((1 : ℝ) / (d : ℝ) ^ 2) := by
    intro d hd
    simp only [Finset.mem_Ioc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
    have hcast : ((x / d : ℕ) : ℝ) ≤ (x : ℝ) / (d : ℝ) := Nat.cast_div_le
    have : ((x / d : ℕ) : ℝ) * ((1 : ℝ) / d) ≤ ((x : ℝ) / d) * ((1 : ℝ) / d) := by
      apply mul_le_mul_of_nonneg_right hcast (by positivity)
    calc ((x / d : ℕ) : ℝ) * ((1 : ℝ) / d) ≤ ((x : ℝ) / d) * ((1 : ℝ) / d) := this
      _ = (x : ℝ) * ((1 : ℝ) / (d : ℝ) ^ 2) := by field_simp
  calc ∑ n ∈ Finset.Ioc 0 x, (sigma 1 n : ℝ) / n
      = ∑ d ∈ Finset.Ioc 0 x, ((x / d : ℕ) : ℝ) * ((1 : ℝ) / d) := h1
    _ ≤ ∑ d ∈ Finset.Ioc 0 x, (x : ℝ) * ((1 : ℝ) / (d : ℝ) ^ 2) := Finset.sum_le_sum h2
    _ = (x : ℝ) * ∑ d ∈ Finset.Ioc 0 x, (1 : ℝ) / (d : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (x : ℝ) * 2 := by
        have hx : (0 : ℝ) ≤ x := Nat.cast_nonneg x
        have hle : ∑ d ∈ Finset.Ioc 0 x, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 2 := by
          refine (sum_inv_sq_le x).trans ?_
          have : (0 : ℝ) ≤ 1 / (max x 1 : ℕ) := by positivity
          linarith
        exact mul_le_mul_of_nonneg_left hle hx
    _ = 2 * x := by ring

/-- The counting function of `abundantSet K` as the cardinality of an explicit finset. -/
