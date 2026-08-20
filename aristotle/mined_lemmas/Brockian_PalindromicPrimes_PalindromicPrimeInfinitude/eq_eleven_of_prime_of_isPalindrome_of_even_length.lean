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

theorem eq_eleven_of_prime_of_isPalindrome_of_even_length {p : ℕ} (hp : p.Prime)
    (hpal : IsPalindrome 10 p) (he : Even (Nat.digits 10 p).length) : p = 11 :=
  ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp
    (eleven_dvd_of_isPalindrome_of_even_length hpal he)).symm

/-- Every palindromic prime other than `11` has an odd number of decimal digits. -/
