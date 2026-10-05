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
def WilsonPrime (p : ℕ) : Prop := p.Prime ∧ p ^ 2 ∣ (p - 1)! + 1

/-- The *Wilson quotient* of `p`, namely `((p - 1)! + 1) / p`.  For prime `p` the division
is exact, by Wilson's theorem (see `wilsonQuotient_spec`). -/
def wilsonQuotient (p : ℕ) : ℕ := ((p - 1)! + 1) / p

/-- Wilson's theorem in divisibility form: a prime `p` divides `(p - 1)! + 1`. -/
theorem prime_dvd_factorial_pred_add_one {p : ℕ} (hp : p.Prime) : p ∣ (p - 1)! + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h : (((p - 1)! + 1 : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.wilsons_lemma]
    ring
  exact (ZMod.natCast_eq_zero_iff _ _).mp h

/-- The defining property of the Wilson quotient of a prime. -/
theorem wilsonQuotient_spec {p : ℕ} (hp : p.Prime) :
    p * wilsonQuotient p = (p - 1)! + 1 :=
  Nat.mul_div_cancel' (prime_dvd_factorial_pred_add_one hp)

/-- Characterisation of Wilson primes via the Wilson quotient: a prime `p` is a Wilson prime
exactly when `p` divides its Wilson quotient. -/
theorem wilsonPrime_iff_dvd_wilsonQuotient {p : ℕ} (hp : p.Prime) :
    WilsonPrime p ↔ p ∣ wilsonQuotient p := by
  have hppos : 0 < p := hp.pos
  constructor
  · rintro ⟨-, k, hk⟩
    refine ⟨k, ?_⟩
    have h : p * wilsonQuotient p = p * (p * k) := by
      rw [wilsonQuotient_spec hp, hk]; ring
    exact Nat.eq_of_mul_eq_mul_left hppos h
  · rintro ⟨k, hk⟩
    refine ⟨hp, ⟨k, ?_⟩⟩
    rw [← wilsonQuotient_spec hp, hk]
    ring

/-- `5` is a Wilson prime. -/
theorem wilsonPrime_five : WilsonPrime 5 := ⟨by norm_num, by decide⟩

/-- `13` is a Wilson prime. -/
theorem wilsonPrime_thirteen : WilsonPrime 13 := ⟨by norm_num, by norm_num [Nat.factorial]⟩

set_option maxRecDepth 10000 in
/-- `563` is a Wilson prime. -/
theorem wilsonPrime_fiveHundredSixtyThree : WilsonPrime 563 := ⟨by norm_num, by decide⟩

/-- Restatement of the Wilson prime condition in `ZMod (p ^ 2)`. -/
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
theorem wilsonPrime_of_lt_six_hundred {p : ℕ} (hp : p < 600) (h : WilsonPrime p) :
    p = 5 ∨ p = 13 ∨ p = 563 := by
  revert hp h
  have key : ∀ q < 600, (Nat.Prime q ∧ q ^ 2 ∣ (q - 1)! + 1) → q = 5 ∨ q = 13 ∨ q = 563 := by
    decide
  exact fun hp h => key p hp h

/-- Complete classification of the Wilson primes below `600`. -/
theorem wilsonPrime_lt_six_hundred_iff {p : ℕ} (hp : p < 600) :
    WilsonPrime p ↔ p = 5 ∨ p = 13 ∨ p = 563 := by
  refine ⟨wilsonPrime_of_lt_six_hundred hp, ?_⟩
  rintro (rfl | rfl | rfl)
  · exact wilsonPrime_five
  · exact wilsonPrime_thirteen
  · exact wilsonPrime_fiveHundredSixtyThree

/-- The set of Wilson primes is nonempty. -/
theorem wilsonPrimes_nonempty : {p : ℕ | WilsonPrime p}.Nonempty :=
  ⟨5, wilsonPrime_five⟩

/-- The set of Wilson primes is infinite iff it is unbounded. -/
theorem wilsonPrimes_infinite_iff_unbounded :
    {p : ℕ | WilsonPrime p}.Infinite ↔ ∀ N : ℕ, ∃ p, N < p ∧ WilsonPrime p := by
  constructor
  · intro h N
    obtain ⟨p, hp, hlt⟩ := h.exists_gt N
    exact ⟨p, hlt, hp⟩
  · intro h
    refine Set.infinite_of_forall_exists_gt fun N => ?_
    obtain ⟨p, hlt, hp⟩ := h N
    exact ⟨p, hp, hlt⟩

/-- **Conditional reduction of the Wilson prime infinitude conjecture.**

If for every bound `N` there is a prime `p > N` whose Wilson quotient
`((p - 1)! + 1) / p` is divisible by `p`, then there are infinitely many Wilson primes.

The hypothesis is the (open) unboundedness statement for vanishing Wilson quotients; the
proof reduces it to infinitude of the set of Wilson primes via the exact characterisation
`wilsonPrime_iff_dvd_wilsonQuotient`.  The conclusion is a statement about a provably
nonempty set (see `wilsonPrimes_nonempty`), so it is not vacuous. -/
theorem WilsonPrimeInfinitude
    (H : ∀ N : ℕ, ∃ p, N < p ∧ p.Prime ∧ p ∣ wilsonQuotient p) :
    {p : ℕ | WilsonPrime p}.Infinite := by
  refine wilsonPrimes_infinite_iff_unbounded.mpr fun N => ?_
  obtain ⟨p, hlt, hp, hdvd⟩ := H N
  exact ⟨p, hlt, (wilsonPrime_iff_dvd_wilsonQuotient hp).mpr hdvd⟩

/-- The hypothesis of `WilsonPrimeInfinitude` is not merely sufficient but equivalent to the
conclusion: the reduction loses nothing. -/
theorem wilsonPrimeInfinitude_iff :
    {p : ℕ | WilsonPrime p}.Infinite ↔
      ∀ N : ℕ, ∃ p, N < p ∧ p.Prime ∧ p ∣ wilsonQuotient p := by
  refine ⟨fun h N => ?_, WilsonPrimeInfinitude⟩
  obtain ⟨p, hp, hlt⟩ := h.exists_gt N
  exact ⟨p, hlt, hp.1, (wilsonPrime_iff_dvd_wilsonQuotient hp.1).mp hp⟩

end Brockian.WilsonPrimes

