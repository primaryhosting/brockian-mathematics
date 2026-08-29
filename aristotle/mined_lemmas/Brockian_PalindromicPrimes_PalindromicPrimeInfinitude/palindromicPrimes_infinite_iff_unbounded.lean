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

theorem palindromicPrimes_infinite_iff_unbounded :
    palindromicPrimes.Infinite ↔ ∀ N : ℕ, ∃ p ∈ palindromicPrimes, N < p :=
  Set.infinite_iff_exists_gt

/-! ## Sanity checks -/

example : (11 : ℕ) ∈ palindromicPrimes :=
  ⟨by norm_num, List.Palindrome.of_reverse_eq (by decide)⟩

example : (131 : ℕ) ∈ oddLengthPalindromicPrimes :=
  ⟨by norm_num, List.Palindrome.of_reverse_eq (by decide), by decide⟩

end Brockian.PalindromicPrimes

