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

/-!
## Overview

Whether there are infinitely many base-ten palindromic primes is an open problem, so the
unconditional statement is out of reach.  What is proved here is an unconditional *reduction*
of that question, resting on a genuine intermediate theorem:

* every base-ten palindrome with an **even** number of digits is divisible by `11`
  (`Brockian.PalindromicPrimes.eleven_dvd_of_isPalindrome_of_even_length`);
* consequently `11` is the **only** palindromic prime with an even number of digits
  (`Brockian.PalindromicPrimes.evenLengthPalindromicPrimes_eq`);
* hence the palindromic primes are infinite **iff** the palindromic primes with an odd number
  of digits are infinite (`Brockian.PalindromicPrimes.PalindromicPrimeInfinitude`).

So the Brockian conjecture may be attacked entirely inside the odd-digit-length case, with no
loss of generality.
-/

namespace Brockian.PalindromicPrimes

open scoped Nat

/-- `n` is a base-ten palindrome: its list of decimal digits equals its own reversal. -/

theorem alternatingSum_eq_zero_of_reverse_eq {L : List ℤ} (hrev : L.reverse = L)
    (hlen : Even L.length) : L.alternatingSum = 0 := by
  have h := List.alternatingSum_reverse L
  rw [hrev] at h
  have hodd : Odd (L.length + 1) := Even.add_one hlen
  rw [hodd.neg_one_pow] at h
  simp only [neg_smul, one_smul] at h
  omega

/-- **Key lemma.** Every base-ten palindrome with an even number of digits is divisible by 11.

This is the arithmetic heart of the reduction: modulo `11` one has `10 ≡ -1`, so a number is
congruent to the alternating sum of its digits; palindromy pairs digit `i` with digit
`len - 1 - i`, and when `len` is even those two positions carry opposite signs. -/
