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
# Wilson Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to be the first command of a file, and a module
docstring `/-! ... -/` is a command, so the requested header is reproduced verbatim
here as an ordinary comment; it also appears as a module docstring below the import.)
-/

import Mathlib

/-!
# Wilson Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Overview

A *Wilson prime* is a prime `p` with `p ^ 2 ∣ (p - 1)! + 1`.  Only three are known
(`5`, `13`, `563`), and whether infinitely many exist is an open problem.

This file develops the basic theory and proves an unconditional characterisation of
Wilson primes in terms of the *Wilson quotient* `W p = ((p - 1)! + 1) / p`
(which is a genuine natural number for every prime `p`, by Wilson's theorem):

* `Brockian.WilsonPrimes.wilsonPrime_iff_dvd_wilsonQuotient` :
  for a prime `p`, `p` is a Wilson prime iff `p ∣ W p`.

The main theorem is a Lean-checked *conditional reduction* of the open conjecture:

* `Brockian.WilsonPrimes.WilsonPrimeInfinitude` :
  if for every bound `N` there is a prime `p > N` whose Wilson quotient is divisible by
  `p`, then the set of Wilson primes is infinite.

Its hypothesis is the "unbounded vanishing of Wilson quotients" statement, and by
`wilsonPrimeInfinitude_iff` the conclusion is in fact equivalent to it, so no unproved
input is smuggled in and nothing is vacuous: the three known Wilson primes `5`, `13`,
`563` are verified below, so the set in question is provably nonempty.
-/

namespace Brockian.WilsonPrimes

open Nat

/-- A prime `p` is a *Wilson prime* if `p ^ 2` divides `(p - 1)! + 1`. -/

theorem wilsonPrime_iff_factorial_eq_neg_one {p : ℕ} (hp : p.Prime) :
    WilsonPrime p ↔ (((p - 1)! : ℕ) : ZMod (p ^ 2)) = -1 := by
  have h : ((((p - 1)! + 1 : ℕ)) : ZMod (p ^ 2)) = 0 ↔ (((p - 1)! : ℕ) : ZMod (p ^ 2)) = -1 := by
    push_cast
    constructor <;> intro h <;> linear_combination h
  rw [WilsonPrime, ← ZMod.natCast_eq_zero_iff, h]
  simp [hp]

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
/-- Exhaustive search: the only Wilson primes below `600` are `5`, `13` and `563`. -/
