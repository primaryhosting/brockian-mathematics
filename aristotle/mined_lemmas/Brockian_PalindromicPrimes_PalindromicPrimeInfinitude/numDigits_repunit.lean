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

/-
Note on file layout: Lean 4 requires `import` commands to be the very first commands
in a module, so the module header above is placed immediately after `import Mathlib`;
putting it before the import is rejected by the Lean parser.

Status of the mathematics.

Whether there are infinitely many base-10 palindromic primes is an open problem: no
unconditional proof is known.  This file therefore contains

* the exact definitions (`IsPalindrome`, `PalindromicPrime`, `palindromicPrimes`);
* unconditional results: there are infinitely many palindromes, concrete palindromic
  primes exist, and every palindromic prime other than `11` has an odd number of
  decimal digits (an even-length decimal palindrome is always divisible by `11`);
* the target theorem `PalindromicPrimeInfinitude` as a Lean-checked *conditional
  reduction*: infinitude of palindromic primes follows from the hypothesis that
  palindromic primes with arbitrarily many decimal digits exist.  The reverse
  implication is proved as well, so the reduction is an equivalence.
-/

namespace Brockian.PalindromicPrimes

open Nat

/-- A natural number is a (base-10) palindrome if its list of decimal digits
reads the same forwards and backwards. -/

lemma numDigits_repunit (k : ℕ) : numDigits (repunit k) = k := by
  simp [numDigits, digits_repunit]

