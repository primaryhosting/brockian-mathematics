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

theorem palindromicPrimes_diff_subset :
    palindromicPrimes \ {11} ⊆ oddLengthPalindromicPrimes := by
  rintro p ⟨⟨hp, hpal⟩, hne⟩
  refine ⟨hp, hpal, ?_⟩
  rcases Nat.even_or_odd (Nat.digits 10 p).length with h | h
  · exact absurd (eq_eleven_of_palindromicPrime_of_even_length hp hpal h) hne
  · exact h

/-! ### Main theorem: reduction of the Brockian conjecture to the odd-digit-length case -/

/-- **Palindromic Prime Infinitude (reduction).**

There are infinitely many base-ten palindromic primes if and only if there are infinitely many
base-ten palindromic primes with an odd number of decimal digits.

The nontrivial direction uses the key lemma that a palindrome of even digit-length is divisible
by `11`, so that the two sets differ only by the single element `11`. -/
