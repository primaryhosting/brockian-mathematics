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

theorem palindromicPrimes_infinite_iff :
    {p : ℕ | IsPalindromicPrime p}.Infinite ↔
      {p : ℕ | IsPalindromicPrime p ∧ Odd (Nat.digits 10 p).length}.Infinite := by
  constructor
  · intro h
    exact PalindromicPrimeInfinitude (unbounded_of_infinite_palindromicPrimes h)
  · intro h
    exact h.mono (fun p hp => hp.1)

end Brockian.PalindromicPrimes

