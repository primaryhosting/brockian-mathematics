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

lemma digits_length_le_self (n : ℕ) : (Nat.digits 10 n).length ≤ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [Nat.digits_len 10 n (by norm_num) hn]
    exact Nat.log_lt_self 10 hn

/-- A number with at least `N` decimal digits is at least `N`. -/
