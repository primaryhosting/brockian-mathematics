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

theorem alternatingSum_eq_zero_of_palindrome_even
    {l : List ℤ} (hp : l.Palindrome) (hlen : Even l.length) :
    l.alternatingSum = 0 := by
  induction hp with
  | nil => simp
  | singleton x => simp at hlen
  | @cons_concat x m hl ih =>
      rw [List.length_cons, List.length_append, List.length_singleton] at hlen
      have hlen' : Even m.length := by
        rcases hlen with ⟨j, hj⟩
        exact ⟨j - 1, by omega⟩
      rw [List.alternatingSum_cons, alternatingSum_append_singleton, ih hlen',
        hlen'.neg_one_pow]
      ring

