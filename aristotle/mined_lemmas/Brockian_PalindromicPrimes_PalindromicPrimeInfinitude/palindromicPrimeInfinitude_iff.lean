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

theorem palindromicPrimeInfinitude_iff :
    (∀ N : ℕ, ∃ p : ℕ, Nat.Prime p ∧ IsPalindrome 10 p ∧ N ≤ (Nat.digits 10 p).length) ↔
      palindromicPrimes.Infinite := by
  refine ⟨PalindromicPrimeInfinitude, fun hinf N => ?_⟩
  obtain ⟨p, hp, hple⟩ := hinf.exists_gt (10 ^ N)
  exact ⟨p, hp.1, hp.2, le_digits_length_of_pow_le hple.le⟩

/--
Refinement of the reduction to *odd* decimal lengths: since `11` is the only
even-length palindromic prime, the set of palindromic primes is infinite if and only
if there are palindromic primes with arbitrarily many digits and an odd number of digits.
-/
