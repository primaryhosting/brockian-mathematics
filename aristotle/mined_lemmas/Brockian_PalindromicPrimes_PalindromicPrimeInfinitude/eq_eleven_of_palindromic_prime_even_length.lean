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

/-- A natural number is *palindromic* (in base 10) when its list of base-10 digits
is equal to its own reversal. -/

theorem eq_eleven_of_palindromic_prime_even_length {p : ℕ} (hp : p ∈ palindromicPrimes)
    (hlen : Even (Nat.digits 10 p).length) : p = 11 := by
  obtain ⟨hprime, hpal⟩ := hp
  have h11 : 11 ∣ p := eleven_dvd_of_palindrome_even_length hpal hlen
  rcases hprime.eq_one_or_self_of_dvd 11 h11 with h | h
  · omega
  · exact h.symm

/-! ## There are arbitrarily large palindromes -/

/-- The digit list `[1, 0, 0, …, 0, 1]` (with `k` interior zeros). -/
