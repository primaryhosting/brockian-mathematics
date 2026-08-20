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
# Palindromic Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.PalindromicPrimes.PalindromicPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Whether there are infinitely many base-10 palindromic primes is an open problem, so
what is proved here is an unconditional *reduction*: the infinitude of palindromic
primes is equivalent to the existence of arbitrarily large palindromic primes whose
decimal expansion has an **odd** number of digits.

The key intermediate lemma is that a base-10 palindrome with an even number of
digits is divisible by `11`; hence `11` is the only palindromic prime with an even
number of digits.
-/

namespace Brockian.PalindromicPrimes

open List

/-- `n` is a palindrome in base `b` if its list of base-`b` digits reads the same
backwards as forwards. -/

theorem prime_and_isPalindrome_eleven : Nat.Prime 11 ∧ IsPalindrome 10 11 :=
  ⟨by norm_num, List.Palindrome.of_reverse_eq (by norm_num)⟩

/-- **Reduction of the palindromic prime infinitude conjecture.**

There are infinitely many base-10 palindromic primes if and only if there are
arbitrarily large palindromic primes with an odd number of decimal digits. -/
