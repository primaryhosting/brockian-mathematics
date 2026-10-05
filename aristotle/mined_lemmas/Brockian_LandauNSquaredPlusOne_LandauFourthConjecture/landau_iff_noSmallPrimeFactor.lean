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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.LandauNSquaredPlusOne

/-- The set of natural numbers `n` such that `n ^ 2 + 1` is prime.
Landau's fourth problem asserts that this set is infinite; it is open. -/

theorem landau_iff_noSmallPrimeFactor :
    LandauSet.Infinite ↔ NoSmallPrimeFactorCondition := by
  constructor
  · intro hinf N
    obtain ⟨n, hn, hgt⟩ := Set.infinite_iff_exists_gt.mp hinf N
    exact ⟨n, hgt, no_small_prime_factor_of_prime hn⟩
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨n, hgt, hn⟩ := h (max N 1)
    refine ⟨n, prime_of_no_small_prime_factor ?_ hn, lt_of_le_of_lt (le_max_left N 1) hgt⟩
    exact le_of_lt (lt_of_le_of_lt (le_max_right N 1) hgt)

/-- **Landau's fourth conjecture, conditional on the elementary sieve condition
`NoSmallPrimeFactorCondition`.**  Assuming that arbitrarily large `n` have the property
that `n ^ 2 + 1` has no prime factor `p ≤ n`, there are infinitely many primes of the
form `n ^ 2 + 1`.

Landau's fourth problem is open, so the result is stated in this conditional form;
`landau_iff_noSmallPrimeFactor` shows that the hypothesis is in fact *equivalent* to the
conjecture, i.e. this is a faithful reduction and not a weakening. -/
