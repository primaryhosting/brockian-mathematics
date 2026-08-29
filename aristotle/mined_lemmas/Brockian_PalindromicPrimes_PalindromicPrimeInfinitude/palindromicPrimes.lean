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

def palindromicPrimes : Set ℕ := {p | Nat.Prime p ∧ IsPalindrome 10 p}

/-!
## The main reduction

Whether `palindromicPrimes` is infinite is a well-known open problem.  The theorem below is
the (unconditional) reduction of that statement to the statement that palindromic primes are
unbounded, i.e. that for every bound there is a larger palindromic prime.
-/

/-- **Reduction of the palindromic prime infinitude conjecture.**
The set of base-10 palindromic primes is infinite if and only if for every `N` there is a
palindromic prime larger than `N`. -/
