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

/-- `n` is a base-10 palindrome: its list of decimal digits is its own reverse. -/

private lemma alternatingSum_concat (l : List ℤ) (a : ℤ) :
    (l ++ [a]).alternatingSum = l.alternatingSum + (-1) ^ l.length * a := by
  induction l with
  | nil => simp
  | cons b t ih =>
      simp only [List.cons_append, List.alternatingSum_cons, ih, List.length_cons]
      ring

/-- A palindromic list of integers of even length has vanishing alternating sum. -/
