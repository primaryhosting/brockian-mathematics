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

theorem digits_repunit (k : ℕ) :
    Nat.digits 10 (repunit k) = List.replicate (k + 1) 1 := by
  refine Nat.digits_ofDigits 10 (by norm_num) _ (fun l hl => ?_) (fun _ => ?_)
  · rw [List.eq_of_mem_replicate hl]; norm_num
  · rw [List.getLast_replicate]; norm_num

