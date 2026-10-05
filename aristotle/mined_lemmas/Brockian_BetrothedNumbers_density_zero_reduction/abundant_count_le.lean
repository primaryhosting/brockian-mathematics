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

theorem abundant_count_le (K x : ℕ) (hK : 0 < K) :
    (countUpTo (abundantSet K) x : ℝ) ≤ 2 * x / K := by
  classical
  set F : Finset ℕ := {n ∈ Finset.Ioc 0 x | K * n < sigma 1 n} with hF
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hmem : ∀ n ∈ F, (K : ℝ) ≤ (sigma 1 n : ℝ) / n := by
    intro n hn
    simp only [hF, Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨hn0, -⟩, hlt⟩ := hn
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [le_div_iff₀ hn0']
    have : ((K * n : ℕ) : ℝ) ≤ ((sigma 1 n : ℕ) : ℝ) := by exact_mod_cast hlt.le
    push_cast at this
    linarith
  have hcard : (F.card : ℝ) * K ≤ ∑ n ∈ F, (sigma 1 n : ℝ) / n := by
    calc (F.card : ℝ) * K = ∑ _n ∈ F, (K : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ F, (sigma 1 n : ℝ) / n := Finset.sum_le_sum hmem
  have hsub : ∑ n ∈ F, (sigma 1 n : ℝ) / n ≤ ∑ n ∈ Finset.Ioc 0 x, (sigma 1 n : ℝ) / n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro n _ _
    positivity
  have := hcard.trans (hsub.trans (sum_sigma_div_self_le x))
  rw [countUpTo_abundantSet K x, le_div_iff₀ hKR]
  exact this

/-- A criterion for density zero: if the counting function is bounded by `C x` for every
`C > 0` eventually, ... (helper) -/
