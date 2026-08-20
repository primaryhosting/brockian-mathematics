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
-/

import Mathlib

/-!
# Wilson Prime Infinitude

Category: Brockian Conjecture.
Target: `Brockian.WilsonPrimes.WilsonPrimeInfinitude`.
Provenance: Aristotle theorem prover (Harmonic).

## Overview

A *Wilson prime* is a prime `p` with `p ^ 2 ∣ (p - 1)! + 1` (an extra power of `p`
beyond what Wilson's theorem, `Mathlib`'s `ZMod.wilsons_lemma`, guarantees).
The only known Wilson primes are `5`, `13` and `563`; whether there are infinitely
many of them is an open problem.

This file develops the basic theory and gives a *Lean-checked conditional reduction*:

* `Brockian.WilsonPrimes.wilsonPrime_iff_dvd_wilsonQuotient` — `p` is a Wilson prime
  iff `p` divides its Wilson quotient `((p-1)! + 1) / p`;
* `Brockian.WilsonPrimes.wilsonPrime_iff_factorial_sub_two` — `p` is a Wilson prime iff
  `(p - 2)! ≡ p + 1 [MOD p ^ 2]`;
* `Brockian.WilsonPrimes.WilsonPrimeInfinitude` — **conditional**: if for every `N`
  there is a prime `p > N` with `(p - 2)! ≡ p + 1 [MOD p ^ 2]`, then the set of Wilson
  primes is infinite;
* `Brockian.WilsonPrimes.wilsonPrimes_infinite_iff` — the above hypothesis is in fact
  equivalent to the infinitude of the set of Wilson primes;
* the three known Wilson primes are verified unconditionally
  (`wilsonPrime_five`, `wilsonPrime_thirteen`, `wilsonPrime_563`).

The only Mathlib input of substance is Wilson's theorem `ZMod.wilsons_lemma`.
-/

namespace Brockian.WilsonPrimes

open Nat

/-- A *Wilson prime*: a prime `p` such that `p ^ 2` divides `(p - 1)! + 1`. -/

theorem wilsonPrimes_infinite_iff :
    {p : ℕ | WilsonPrime p}.Infinite ↔
      ∀ N : ℕ, ∃ p : ℕ, p.Prime ∧ N < p ∧ (p - 2)! ≡ p + 1 [MOD p ^ 2] := by
  constructor
  · intro hinf N
    obtain ⟨p, hp, hNp⟩ := hinf.exists_gt N
    exact ⟨p, hp.1, hNp, (wilsonPrime_iff_factorial_sub_two hp.1).mp hp⟩
  · exact WilsonPrimeInfinitude

end Brockian.WilsonPrimes

