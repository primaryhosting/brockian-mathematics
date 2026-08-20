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

theorem digits_palNumber (k : ℕ) :
    Nat.digits 10 (Nat.ofDigits 10 (palList k)) = palList k := by
  refine Nat.digits_ofDigits 10 (by norm_num) _ (palList_lt k) ?_
  intro h
  rw [palList_getLast k h]
  norm_num

/-- The number with digits `[1, 0, …, 0, 1]` is a palindrome. -/
