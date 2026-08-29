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

theorem hasDensityZero_iff (S : Set ℕ) :
    HasDensityZero S ↔ ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in Filter.atTop,
      (countUpTo S x : ℝ) / x < ε := by
  constructor
  · intro h ε hε
    have := (Metric.tendsto_atTop.mp (show Filter.Tendsto _ _ _ from h)) ε hε
    obtain ⟨N, hN⟩ := this
    filter_upwards [Filter.eventually_ge_atTop N] with x hx
    have := hN x hx
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  · intro h
    rw [HasDensityZero, Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h ε hε)
    refine ⟨N, fun x hx => ?_⟩
    have hpos : (0 : ℝ) ≤ (countUpTo S x : ℝ) / x := by positivity
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hpos]
    exact hN x hx

end BetrothedNumbers
end Brockian

/-
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Basic definitions for betrothed (quasi-amicable) numbers

A pair `(m, n)` of positive integers is *betrothed* (or *quasi-amicable*) if
`σ m = σ n = m + n + 1`, i.e. each of the two numbers is the sum of the
non-trivial proper divisors of the other.  This file sets up the basic
definitions, the elementary structure theory of such pairs (in particular the
fact that the partner of a betrothed number is *determined* by the number),
and the notion of asymptotic density zero used in the main reduction theorem.
-/

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction Finset

/-- `(m, n)` is a betrothed (quasi-amicable) pair: both are positive and
`σ m = σ n = m + n + 1`. -/
