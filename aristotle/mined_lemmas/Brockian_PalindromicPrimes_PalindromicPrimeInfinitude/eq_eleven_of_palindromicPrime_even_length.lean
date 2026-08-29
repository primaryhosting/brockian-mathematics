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
-- (Lean 4 requires `import` to precede any module docstring `/-! ... -/`, so the header above
-- is given as a plain block comment and repeated as the module docstring below.)

import Mathlib

/-!
# Palindromic Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.PalindromicPrimes.PalindromicPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PalindromicPrimes

/-- `n` is a palindrome in base `b`: its list of base-`b` digits is its own reverse. -/

theorem eq_eleven_of_palindromicPrime_even_length {p : ℕ} (hp : PalindromicPrime p)
    (hlen : Even (Nat.digits 10 p).length) : p = 11 := by
  obtain ⟨hprime, hpal⟩ := hp
  have h11 : 11 ∣ p := eleven_dvd_of_palindromic_even_length hpal hlen
  rcases hprime.eq_one_or_self_of_dvd 11 h11 with h | h
  · omega
  · exact h.symm

/-- The base-ten repunit with `k` digits. -/
