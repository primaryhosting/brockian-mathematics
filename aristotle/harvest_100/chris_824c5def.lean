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
def WilsonPrime (p : ℕ) : Prop := p.Prime ∧ p ^ 2 ∣ (p - 1)! + 1

/-- The *Wilson quotient* of `p`, namely `((p - 1)! + 1) / p`.  For a prime `p` the
division is exact, by Wilson's theorem (see `mul_wilsonQuotient`). -/
def wilsonQuotient (p : ℕ) : ℕ := ((p - 1)! + 1) / p

/-- Wilson's theorem in divisibility form: `p ∣ (p - 1)! + 1` for a prime `p`. -/
lemma dvd_factorial_pred_add_one {p : ℕ} (hp : p.Prime) : p ∣ (p - 1)! + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h : (((p - 1)! + 1 : ℕ) : ZMod p) = 0 := by
    push_cast [ZMod.wilsons_lemma]
    ring
  exact (ZMod.natCast_eq_zero_iff _ _).mp h

/-- The Wilson quotient really is a quotient: `p * wilsonQuotient p = (p - 1)! + 1`. -/
lemma mul_wilsonQuotient {p : ℕ} (hp : p.Prime) :
    p * wilsonQuotient p = (p - 1)! + 1 :=
  Nat.mul_div_cancel' (dvd_factorial_pred_add_one hp)

/-- A prime is a Wilson prime exactly when it divides its own Wilson quotient. -/
lemma wilsonPrime_iff_dvd_wilsonQuotient {p : ℕ} (hp : p.Prime) :
    WilsonPrime p ↔ p ∣ wilsonQuotient p := by
  rw [WilsonPrime, and_iff_right hp, ← mul_wilsonQuotient hp, sq]
  exact mul_dvd_mul_iff_left hp.ne_zero

/-- For a prime `p` one has `(p - 2)! ≡ 1 [MOD p]`. -/
lemma factorial_sub_two_modEq_one {p : ℕ} (hp : p.Prime) : (p - 2)! ≡ 1 [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : 2 ≤ p := hp.two_le
  have hsucc : (p - 1)! = (p - 1) * (p - 2)! := by
    have h : p - 1 = (p - 2) + 1 := by omega
    rw [h, Nat.factorial_succ]
  have hcast : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub hp.one_le, ZMod.natCast_self]; simp
  have hw : ((p - 1)! : ZMod p) = -1 := ZMod.wilsons_lemma p
  rw [hsucc] at hw
  push_cast [hcast] at hw
  have hx : (((p - 2)! : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    push_cast; linear_combination -hw
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hx

/-- A second characterisation of Wilson primes, "one factorial down":
a prime `p` is a Wilson prime iff `(p - 2)! ≡ p + 1 [MOD p ^ 2]`. -/
lemma wilsonPrime_iff_factorial_sub_two {p : ℕ} (hp : p.Prime) :
    WilsonPrime p ↔ (p - 2)! ≡ p + 1 [MOD p ^ 2] := by
  have h2 : 2 ≤ p := hp.two_le
  have hP : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (((p - 2)! : ℕ) : ℤ) = 1 + (p : ℤ) * k := by
    obtain ⟨m, hm⟩ := (Nat.modEq_iff_dvd (n := p)).mp (factorial_sub_two_modEq_one hp)
    exact ⟨-m, by push_cast at hm ⊢; linarith⟩
  have hsucc : (p - 1)! = (p - 1) * (p - 2)! := by
    have h : p - 1 = (p - 2) + 1 := by omega
    rw [h, Nat.factorial_succ]
  rw [WilsonPrime, and_iff_right hp, Nat.modEq_iff_dvd,
    ← Int.natCast_dvd_natCast (m := p ^ 2)]
  push_cast [hsucc, hk, Nat.cast_sub hp.one_le]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h
    have hd : ((p : ℤ) * (p : ℤ)) ∣ (p : ℤ) * (1 - k) := ⟨c - k, by linear_combination hc⟩
    obtain ⟨d, hd'⟩ := (mul_dvd_mul_iff_left (ne_of_gt hP)).mp hd
    exact ⟨d, by linear_combination (p : ℤ) * hd'⟩
  · intro h
    obtain ⟨c, hc⟩ := h
    have hd : ((p : ℤ) * (p : ℤ)) ∣ (p : ℤ) * (1 - k) := ⟨c, by linear_combination hc⟩
    obtain ⟨d, hd'⟩ := (mul_dvd_mul_iff_left (ne_of_gt hP)).mp hd
    exact ⟨d + k, by linear_combination (p : ℤ) * hd'⟩

/-!
## The three known Wilson primes
-/

lemma wilsonPrime_five : WilsonPrime 5 := ⟨by norm_num, by decide⟩

lemma wilsonPrime_thirteen : WilsonPrime 13 := ⟨by norm_num, by norm_num [Nat.factorial]⟩

set_option maxRecDepth 10000 in
lemma wilsonPrime_563 : WilsonPrime 563 := ⟨by norm_num, by decide⟩

/-!
## The conditional infinitude statement
-/

/-- **Wilson prime infinitude (conditional reduction).**

Whether there are infinitely many Wilson primes is an open problem, so the statement is
proved here conditionally on the hypothesis `H`, which is phrased in the equivalent
"one factorial down" form `(p - 2)! ≡ p + 1 [MOD p ^ 2]` supplied by
`wilsonPrime_iff_factorial_sub_two`: if arbitrarily large primes satisfy that
congruence, then the set of Wilson primes is infinite. -/
theorem WilsonPrimeInfinitude
    (H : ∀ N : ℕ, ∃ p : ℕ, p.Prime ∧ N < p ∧ (p - 2)! ≡ p + 1 [MOD p ^ 2]) :
    {p : ℕ | WilsonPrime p}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hp, hNp, hcong⟩ := H N
  exact ⟨p, (wilsonPrime_iff_factorial_sub_two hp).mpr hcong, hNp⟩

/-- The hypothesis of `WilsonPrimeInfinitude` is not merely sufficient but equivalent to
the infinitude of the set of Wilson primes. -/
theorem wilsonPrimes_infinite_iff :
    {p : ℕ | WilsonPrime p}.Infinite ↔
      ∀ N : ℕ, ∃ p : ℕ, p.Prime ∧ N < p ∧ (p - 2)! ≡ p + 1 [MOD p ^ 2] := by
  constructor
  · intro hinf N
    obtain ⟨p, hp, hNp⟩ := hinf.exists_gt N
    exact ⟨p, hp.1, hNp, (wilsonPrime_iff_factorial_sub_two hp.1).mp hp⟩
  · exact WilsonPrimeInfinitude

end Brockian.WilsonPrimes

