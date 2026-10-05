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

namespace Brockian.PalindromicPrimes

open Nat

/-- A natural number is a (base-10) palindrome when its list of decimal digits
reads the same forwards and backwards. -/

theorem evenLengthPalindromicPrimes_subset_singleton :
    {p : ℕ | Nat.Prime p ∧ IsPalindrome p ∧ Even (Nat.digits 10 p).length} ⊆ {11} := by
  rintro p ⟨hp, hpal, he⟩
  exact eq_eleven_of_even_length hp hpal he

/-- **Conditional reduction for the infinitude of palindromic primes.**

There are infinitely many palindromic primes if and only if there are
infinitely many palindromic primes with an *odd* number of decimal digits.

(The unconditional infinitude statement is a well-known open problem; this is a
Lean-checked reduction of it, obtained from the fact that every base-10
palindrome with an even number of digits is divisible by `11`.) -/
