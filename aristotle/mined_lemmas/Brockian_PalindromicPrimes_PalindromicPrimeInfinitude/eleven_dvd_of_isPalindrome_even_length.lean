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

theorem eleven_dvd_of_isPalindrome_even_length {n : ℕ} (hpal : IsPalindrome 10 n)
    (hlen : Even (Nat.digits 10 n).length) : 11 ∣ n := by
  have hzero : ((Nat.digits 10 n).map (fun m : ℕ => (m : ℤ))).alternatingSum = 0 := by
    refine alternatingSum_eq_zero_of_palindrome_even (List.Palindrome.of_reverse_eq ?_) ?_
    · rw [← List.map_reverse, hpal]
    · simpa using hlen
  rw [Nat.eleven_dvd_iff, hzero]
  exact dvd_zero 11

/-- `11` is the only base-10 palindromic prime with an even number of digits. -/
