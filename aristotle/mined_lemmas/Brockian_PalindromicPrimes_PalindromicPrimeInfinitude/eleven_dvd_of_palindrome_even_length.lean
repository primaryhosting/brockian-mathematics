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

theorem eleven_dvd_of_palindrome_even_length {n : ℕ} (hp : IsPalindrome 10 n)
    (hlen : Even (Nat.digits 10 n).length) : 11 ∣ n := by
  rw [Nat.eleven_dvd_iff]
  have hrev : ((Nat.digits 10 n).map (fun d : ℕ => (d : ℤ))).reverse
      = (Nat.digits 10 n).map (fun d : ℕ => (d : ℤ)) := by
    rw [← List.map_reverse, hp]
  have hlen' : Even ((Nat.digits 10 n).map (fun d : ℕ => (d : ℤ))).length := by
    simpa using hlen
  rw [alternatingSum_eq_zero_of_palindrome_even _ hrev hlen']
  exact dvd_zero 11

/-- The only base-10 palindromic prime with an even number of digits is `11`.
Hence, apart from `11`, every palindromic prime has an odd number of digits. -/
