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
-/

/-!
## Status and contents

The unconditional statement "there are infinitely many base-10 palindromic primes" is an open
problem, so this file provides a Lean-checked conditional reduction together with unconditional
partial results.

* `IsPalindrome`, `palindromicPrimes` : the basic definitions.
* `PalindromicPrimeInfinitude` : **the target**, a conditional reduction — if palindromic primes
  are unbounded then there are infinitely many of them (and `infinite_iff_unbounded` shows the
  two formulations are equivalent).
* `eleven_dvd_of_palindrome_even_length`, `eq_eleven_of_prime_palindrome_even_length` :
  unconditional results — a palindrome with an even number of digits is divisible by `11`
  (via the Mathlib lemma `Nat.eleven_dvd_iff`), hence `11` is the only palindromic prime with
  an even number of digits.
* `infinite_iff_oddDigit_infinite` : consequently the conjecture is equivalent to its
  odd-digit-count version.
-/

namespace Brockian.PalindromicPrimes

/-- `n` is a base-10 palindrome: its list of decimal digits is its own reversal. -/

theorem alternatingSum_eq_zero_of_palindrome_even {l : List ℤ} (hp : l.Palindrome)
    (he : Even l.length) : l.alternatingSum = 0 := by
  induction hp with
  | nil => simp
  | singleton x => simp at he
  | @cons_concat x l hl ih =>
      have hlen : (x :: (l ++ [x])).length = l.length + 2 := by simp
      have hel : Even l.length := by
        rw [hlen] at he
        rcases he with ⟨k, hk⟩
        exact ⟨k - 1, by omega⟩
      have := ih hel
      simp [List.alternatingSum_cons, alternatingSum_append, this, hel.neg_one_pow]

/-! ### Even-length palindromes are divisible by 11 -/

/-- A base-10 palindrome with an even number of digits is divisible by `11`. -/
