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

theorem eleven_dvd_of_palindrome_even_length {n : ℕ} (hp : IsPalindrome n)
    (hlen : Even (Nat.digits 10 n).length) : 11 ∣ n := by
  rw [Nat.eleven_dvd_iff]
  have hrev : (List.map (fun m : ℕ => (m : ℤ)) (Nat.digits 10 n)).reverse
      = List.map (fun m : ℕ => (m : ℤ)) (Nat.digits 10 n) := by
    rw [← List.map_reverse, hp]
  have hlen' : Even (List.map (fun m : ℕ => (m : ℤ)) (Nat.digits 10 n)).length := by
    simpa using hlen
  rw [alternatingSum_eq_zero_of_palindrome_even _ hrev hlen']
  simp

/-- The only palindromic prime with an even number of base-10 digits is `11`. -/
