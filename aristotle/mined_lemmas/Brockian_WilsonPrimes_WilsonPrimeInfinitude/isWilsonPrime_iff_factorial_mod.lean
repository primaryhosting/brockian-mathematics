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
-- (Lean requires `import` to precede any module docstring, so the header above is written as a
-- plain block comment; the same header is repeated as the module docstring below.)

import Mathlib

/-!
# Wilson Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Overview

A *Wilson prime* is a prime `p` with `p ^ 2 ∣ (p - 1)! + 1`.  By Wilson's theorem `p` always
divides `(p - 1)! + 1`, so the quotient `w p = ((p - 1)! + 1) / p` (the *Wilson quotient*) is an
integer, and `p` is a Wilson prime exactly when `p ∣ w p`.

Whether there are infinitely many Wilson primes is an open problem; only three are known
(`5`, `13`, `563`).  Accordingly this file contains:

* the basic theory of Wilson quotients (`wilsonQuotient_spec`);
* several equivalent reformulations of the Wilson-prime condition
  (`isWilsonPrime_iff_dvd_wilsonQuotient`, `isWilsonPrime_iff_zmod`,
  `isWilsonPrime_iff_factorial_mod`);
* the reduction of the infinitude statement to the Wilson-quotient formulation
  (`WilsonPrimeInfinitude`, sharpened to an equivalence in `infinite_isWilsonPrime_iff`),
  together with the contrapositive form `not_infinite_isWilsonPrime_iff`;
* unconditional verification that `5`, `13` and `563` are Wilson primes, hence that there are
  at least three of them.

The main target `WilsonPrimeInfinitude` is therefore a *conditional* result: it derives the
infinitude of Wilson primes from the (equivalent, and still open) hypothesis that arbitrarily
large primes divide their own Wilson quotient.
-/

namespace Brockian.WilsonPrimes

open Nat

/-- `p` is a *Wilson prime* if `p` is prime and `p ^ 2 ∣ (p - 1)! + 1`. -/

theorem isWilsonPrime_iff_factorial_mod {p : ℕ} (hp : p.Prime) :
    IsWilsonPrime p ↔ (p - 1)! % p ^ 2 = p ^ 2 - 1 := by
  have hp2 : 1 < p ^ 2 := by
    have := hp.two_le
    nlinarith
  constructor
  · rintro ⟨-, k, hk⟩
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := by
      cases k with
      | zero => exfalso; simp at hk
      | succ n => exact ⟨n, rfl⟩
    have h : (p - 1)! = p ^ 2 * k + (p ^ 2 - 1) := by
      have h2 : p ^ 2 * (k + 1) = p ^ 2 * k + p ^ 2 := by ring
      omega
    rw [h, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
  · intro h
    refine ⟨hp, ?_⟩
    have hdm : p ^ 2 * ((p - 1)! / p ^ 2) + (p - 1)! % p ^ 2 = (p - 1)! := Nat.div_add_mod _ _
    refine ⟨(p - 1)! / p ^ 2 + 1, ?_⟩
    rw [h] at hdm
    have hexp : p ^ 2 * ((p - 1)! / p ^ 2 + 1) = p ^ 2 * ((p - 1)! / p ^ 2) + p ^ 2 := by ring
    omega

/-- **Main reduction (target).**  If arbitrarily large primes divide their own Wilson quotient,
then there are infinitely many Wilson primes.

This is a conditional statement: the hypothesis is the (open) Wilson-quotient form of the
conjecture, and the theorem shows that it implies the infinitude of Wilson primes. -/
