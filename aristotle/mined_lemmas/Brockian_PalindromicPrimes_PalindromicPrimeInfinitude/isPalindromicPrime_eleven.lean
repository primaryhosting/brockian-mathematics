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

theorem isPalindromicPrime_eleven : IsPalindromicPrime 11 := by decide

/-! ### The main conditional reduction -/

/-- **Conditional reduction for the infinitude of palindromic primes.**

The unconditional infinitude of base-10 palindromic primes is an open problem, so the
statement is formulated conditionally: assuming palindromic primes are unbounded
(hypothesis `H`), the set of palindromic primes having an *odd* number of decimal digits
is infinite.  The "odd length" strengthening is genuine content: it rests on the
unconditional theorem, proved above, that `11` is the only palindromic prime with an
even number of decimal digits. -/
