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

/-- `n` is a palindrome in base `b` if its list of base-`b` digits is equal to its reverse. -/

theorem infinite_palindromes : {n : ℕ | IsPalindrome 10 n}.Infinite := by
  have hinj : Function.Injective fun k : ℕ => Nat.ofDigits 10 (onePad k) := by
    intro a b hab
    have hlist : onePad a = onePad b := by
      rw [← digits_ofDigits_onePad a, ← digits_ofDigits_onePad b]
      simp only at hab
      rw [hab]
    have := congrArg List.length hlist
    rw [length_onePad, length_onePad] at this
    omega
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => Nat.ofDigits 10 (onePad k))
    hinj ?_
  intro k
  exact isPalindrome_ofDigits_onePad k

/-!
### Even-length palindromic primes

Every base-10 palindrome with an even number of digits is divisible by 11; consequently `11`
is the only palindromic prime with an even number of digits.
-/

