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
# Palindromic Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.PalindromicPrimes.PalindromicPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.PalindromicPrimes

/-- `n` is a palindrome in base `b` if its list of base-`b` digits is equal to its reverse. -/

theorem odd_length_digits_of_palindromic_prime {p : ℕ} (hp : Nat.Prime p)
    (hpal : IsPalindrome 10 p) (hne : p ≠ 11) : Odd (Nat.digits 10 p).length := by
  rcases Nat.even_or_odd (Nat.digits 10 p).length with h | h
  · exact absurd (eq_eleven_of_palindromic_prime_even_length hp hpal h) hne
  · exact h

/-!
### Concrete palindromic primes
-/

