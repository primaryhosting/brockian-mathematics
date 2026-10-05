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

theorem eq_eleven_of_palindromic_prime_even_length {p : ℕ} (hp : Nat.Prime p)
    (hpal : IsPalindrome 10 p) (hlen : Even (Nat.digits 10 p).length) : p = 11 := by
  have h11 : 11 ∣ p := eleven_dvd_of_isPalindrome_even_length hpal hlen
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp 11 h11) with h | h
  · norm_num at h
  · exact h.symm

/-- Every palindromic prime other than `11` has an odd number of digits. -/
