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

import Mathlib

/-!
# Palindromic Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.PalindromicPrimes.PalindromicPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PalindromicPrimes

/-- `IsPalindrome b n` says that the base-`b` digit expansion of `n` reads the same
forwards and backwards. -/

theorem palindromicPrimeInfinitude_odd_length :
    (∀ N : ℕ, ∃ p : ℕ, Nat.Prime p ∧ IsPalindrome 10 p ∧ N ≤ (Nat.digits 10 p).length ∧
        Odd (Nat.digits 10 p).length) ↔ palindromicPrimes.Infinite := by
  rw [← palindromicPrimeInfinitude_iff]
  constructor
  · intro H N
    obtain ⟨p, hprime, hpal, hlen, -⟩ := H N
    exact ⟨p, hprime, hpal, hlen⟩
  · intro H N
    have hinf : palindromicPrimes.Infinite := PalindromicPrimeInfinitude H
    obtain ⟨p, hp, hgt⟩ := hinf.exists_gt (max (10 ^ N) 11)
    have hpow : 10 ^ N ≤ p := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hgt)
    have hodd : Odd (Nat.digits 10 p).length := by
      rw [Nat.not_even_iff_odd.symm]
      intro heven
      have : p = 11 := eq_eleven_of_prime_palindrome_even_length hp.1 hp.2 heven
      have : (11 : ℕ) < p := lt_of_le_of_lt (le_max_right _ _) hgt
      omega
    exact ⟨p, hp.1, hp.2, le_digits_length_of_pow_le hpow, hodd⟩

end Brockian.PalindromicPrimes

