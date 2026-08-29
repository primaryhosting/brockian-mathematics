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

theorem sigma_div_self (n : ℕ) (hn : 0 < n) :
    (sigma 1 n : ℝ) / n = ∑ d ∈ n.divisors, (1 : ℝ) / d := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [← Nat.sum_div_divisors n (fun d => (1 : ℝ) / d)]
  rw [sigma_one_apply, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [Nat.mem_divisors] at hd
  obtain ⟨hdvd, -⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
  have : ((n / d : ℕ) : ℝ) = (n : ℝ) / (d : ℝ) := by
    rw [Nat.cast_div hdvd (by exact_mod_cast hd0.ne')]
  rw [this, one_div_div]

/-- `∑_{0 < d ≤ x} 1/d² ≤ 2 - 1/max x 1`. -/
