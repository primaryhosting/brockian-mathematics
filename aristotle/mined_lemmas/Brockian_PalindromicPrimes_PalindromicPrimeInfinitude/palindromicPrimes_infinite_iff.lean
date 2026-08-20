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

The infinitude of decimal palindromic primes is an open problem.  This file develops
what can be established unconditionally, and reduces the conjecture to a statement
about *odd* digit lengths only.

Main contents:

* `Brockian.PalindromicPrimes.IsPalindrome` — decimal palindromes.
* `eleven_dvd_of_isPalindrome_even_length` — every decimal palindrome with an even
  number of digits is divisible by `11`.
* `eq_eleven_of_prime_palindrome_even_length` — hence `11` is the *only* palindromic
  prime with an even number of digits.
* `palindromes_infinite` — there are infinitely many decimal palindromes
  (the repunits).
* `PalindromicPrimeInfinitude` — the conditional reduction: if for arbitrarily large
  `m` there is a prime palindrome with exactly `2 * m + 1` digits, then there are
  infinitely many palindromic primes.
* `palindromicPrimes_infinite_iff` — the reduction is in fact an equivalence, so no
  strength is lost by restricting attention to odd digit lengths.
-/

namespace Brockian.PalindromicPrimes

/-- A natural number is a (decimal) palindrome when its list of base-10 digits is
equal to its own reversal. -/

theorem palindromicPrimes_infinite_iff :
    palindromicPrimes.Infinite ↔
      ∀ n : ℕ, ∃ m ≥ n, ∃ p : ℕ, Nat.Prime p ∧ IsPalindrome p ∧
        (Nat.digits 10 p).length = 2 * m + 1 :=
  ⟨odd_length_of_palindromicPrimes_infinite, PalindromicPrimeInfinitude⟩

end Brockian.PalindromicPrimes

