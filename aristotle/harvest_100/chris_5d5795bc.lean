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
def IsWilsonPrime (p : ℕ) : Prop := p.Prime ∧ p ^ 2 ∣ (p - 1)! + 1

/-- The *Wilson quotient* of `p`, namely `((p - 1)! + 1) / p`.  For prime `p` this is an exact
division, by Wilson's theorem (see `wilsonQuotient_spec`). -/
def wilsonQuotient (p : ℕ) : ℕ := ((p - 1)! + 1) / p

/-- **Wilson's theorem**, in divisibility form: a prime `p` divides `(p - 1)! + 1`. -/
theorem dvd_factorial_pred_add_one {p : ℕ} (hp : p.Prime) : p ∣ (p - 1)! + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h : (((p - 1)! + 1 : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.wilsons_lemma]
    ring
  exact (ZMod.natCast_eq_zero_iff _ _).1 h

/-- The defining property of the Wilson quotient of a prime. -/
theorem wilsonQuotient_spec {p : ℕ} (hp : p.Prime) : p * wilsonQuotient p = (p - 1)! + 1 :=
  Nat.mul_div_cancel' (dvd_factorial_pred_add_one hp)

/-- **Reformulation.** A prime is a Wilson prime exactly when it divides its Wilson quotient. -/
theorem isWilsonPrime_iff_dvd_wilsonQuotient {p : ℕ} (hp : p.Prime) :
    IsWilsonPrime p ↔ p ∣ wilsonQuotient p := by
  have hp0 : p ≠ 0 := hp.ne_zero
  constructor
  · rintro ⟨-, hdvd⟩
    rw [← wilsonQuotient_spec hp, sq] at hdvd
    exact (mul_dvd_mul_iff_left hp0).1 hdvd
  · intro h
    refine ⟨hp, ?_⟩
    rw [← wilsonQuotient_spec hp, sq]
    exact mul_dvd_mul_left p h

/-- **Reformulation.** A prime `p` is a Wilson prime exactly when `(p - 1)! = -1` in
`ZMod (p ^ 2)`. -/
theorem isWilsonPrime_iff_zmod {p : ℕ} (hp : p.Prime) :
    IsWilsonPrime p ↔ (((p - 1)! : ℕ) : ZMod (p ^ 2)) = -1 := by
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hcast : (((p - 1)! + 1 : ℕ) : ZMod (p ^ 2)) = 0 ↔ p ^ 2 ∣ (p - 1)! + 1 :=
    ZMod.natCast_eq_zero_iff _ _
  push_cast at hcast
  have key : (((p - 1)! : ℕ) : ZMod (p ^ 2)) = -1 ↔ p ^ 2 ∣ (p - 1)! + 1 :=
    eq_neg_iff_add_eq_zero.trans hcast
  exact ⟨fun h => key.2 h.2, fun h => ⟨hp, key.1 h⟩⟩

/-- **Reformulation.** A prime `p` is a Wilson prime exactly when `(p - 1)! ≡ p ^ 2 - 1`
modulo `p ^ 2`. -/
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
theorem WilsonPrimeInfinitude
    (h : ∀ N : ℕ, ∃ p > N, p.Prime ∧ p ∣ wilsonQuotient p) :
    {p : ℕ | IsWilsonPrime p}.Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro N
  obtain ⟨p, hpN, hp, hdvd⟩ := h N
  exact ⟨p, (isWilsonPrime_iff_dvd_wilsonQuotient hp).2 hdvd, hpN⟩

/-- The hypothesis of `WilsonPrimeInfinitude` is in fact equivalent to its conclusion: the
Wilson-quotient formulation is a faithful reformulation of the conjecture. -/
theorem infinite_isWilsonPrime_iff :
    {p : ℕ | IsWilsonPrime p}.Infinite ↔ ∀ N : ℕ, ∃ p > N, p.Prime ∧ p ∣ wilsonQuotient p := by
  refine ⟨fun hinf N => ?_, WilsonPrimeInfinitude⟩
  obtain ⟨p, hp, hpN⟩ := hinf.exists_gt N
  exact ⟨p, hpN, hp.1, (isWilsonPrime_iff_dvd_wilsonQuotient hp.1).1 hp⟩

/-- **Contrapositive form.**  There are only finitely many Wilson primes iff beyond some bound no
prime divides its Wilson quotient. -/
theorem not_infinite_isWilsonPrime_iff :
    ¬ {p : ℕ | IsWilsonPrime p}.Infinite ↔
      ∃ N : ℕ, ∀ p > N, p.Prime → ¬ p ∣ wilsonQuotient p := by
  rw [infinite_isWilsonPrime_iff]
  push_neg
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, fun p hp hpp hdvd => hN p hp hpp hdvd⟩
  · rintro ⟨N, hN⟩
    exact ⟨N, fun p hp hpp => hN p hp hpp⟩

section Examples

/-- `5` is a Wilson prime. -/
theorem isWilsonPrime_five : IsWilsonPrime 5 := ⟨by norm_num, by decide⟩

/-- `13` is a Wilson prime. -/
theorem isWilsonPrime_thirteen : IsWilsonPrime 13 := ⟨by norm_num, by decide⟩

set_option maxRecDepth 10000 in
/-- `563` is a Wilson prime. -/
theorem isWilsonPrime_563 : IsWilsonPrime 563 := by
  refine ⟨by norm_num, Nat.dvd_of_mod_eq_zero ?_⟩
  decide

/-- Unconditionally, there are at least three Wilson primes. -/
theorem exists_three_wilsonPrimes :
    ∃ S : Finset ℕ, S.card = 3 ∧ ∀ p ∈ S, IsWilsonPrime p := by
  refine ⟨{5, 13, 563}, by decide, ?_⟩
  intro p hp
  fin_cases hp
  · exact isWilsonPrime_five
  · exact isWilsonPrime_thirteen
  · exact isWilsonPrime_563

end Examples

end Brockian.WilsonPrimes

