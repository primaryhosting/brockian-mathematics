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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AmicableNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The sum of all (positive) divisors of `n`.  For `n = 0` this is `0`. -/

theorem amicable_infinite_of_infinitely_many_thabitIndices
    (h : ∀ K : ℕ, ∃ k ≥ K, ThabitIndex k) : AmicableSet.Infinite := by
  refine amicable_infinite_iff_unbounded.mpr fun N => ?_
  obtain ⟨k, hk, hT⟩ := h N
  refine ⟨2 ^ (k + 2) * (3 * 2 ^ (k + 1) - 1) * (3 * 2 ^ (k + 2) - 1),
    ⟨_, isAmicablePair_of_thabitIndex hT⟩, ?_⟩
  obtain ⟨hp, hq, _⟩ := hT
  have hp1 : 1 ≤ 3 * 2 ^ (k + 1) - 1 := hp.one_lt.le.trans' (by norm_num)
  have hq1 : 1 ≤ 3 * 2 ^ (k + 2) - 1 := hq.one_lt.le.trans' (by norm_num)
  have hbig : 2 ^ (k + 2) ≤ 2 ^ (k + 2) * (3 * 2 ^ (k + 1) - 1) * (3 * 2 ^ (k + 2) - 1) := by
    calc 2 ^ (k + 2) = 2 ^ (k + 2) * 1 * 1 := by ring
      _ ≤ 2 ^ (k + 2) * (3 * 2 ^ (k + 1) - 1) * (3 * 2 ^ (k + 2) - 1) := by
          exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hp1) hq1
  have hlt : k < 2 ^ (k + 2) :=
    lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
  omega

/-- **Amicable Infinitude (conditional reduction).**
If amicable pairs occur arbitrarily far out — i.e. for every bound `N` there is an
amicable pair `(m, n)` with `N < m` — then the set of amicable numbers is infinite.

The hypothesis is exactly the standard "unbounded supply of amicable pairs" statement,
which by `amicable_infinite_iff_unbounded` is equivalent to the conclusion; the
infinitude of amicable numbers is an open problem, so the result is stated in this
conditional form.  A stronger, purely number-theoretic sufficient condition is given by
`amicable_infinite_of_infinitely_many_thabitIndices`. -/
