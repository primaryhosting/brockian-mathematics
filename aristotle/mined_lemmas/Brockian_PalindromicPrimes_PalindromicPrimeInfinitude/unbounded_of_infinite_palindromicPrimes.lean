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
# Palindromic Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.PalindromicPrimes.PalindromicPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PalindromicPrimes

/-- `n` is a base-10 palindrome: its list of decimal digits is its own reverse. -/

theorem unbounded_of_infinite_palindromicPrimes
    (h : {p : ℕ | IsPalindromicPrime p}.Infinite) :
    ∀ N : ℕ, ∃ p : ℕ, N < p ∧ IsPalindromicPrime p := by
  intro N
  obtain ⟨p, hp, hlt⟩ := h.exists_gt N
  exact ⟨p, hlt, hp⟩

/-- The infinitude of palindromic primes is equivalent to their unboundedness, and is
also equivalent to the infinitude of the odd-digit-length palindromic primes. -/
