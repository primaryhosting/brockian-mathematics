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

/-!
# Wilson Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Nat

namespace Brockian.WilsonPrimes

/-- A *Wilson prime* is a prime `p` with `p ^ 2 ∣ (p - 1)! + 1`
(the ordinary Wilson congruence `p ∣ (p-1)! + 1` holds for every prime). -/
def IsWilsonPrime (p : ℕ) : Prop := p.Prime ∧ p ^ 2 ∣ (p - 1)! + 1

/-- The *Wilson quotient* of `p`, namely `((p-1)! + 1) / p`.  For a prime `p` this division
is exact, by Wilson's theorem. -/
def wilsonQuotient (p : ℕ) : ℕ := ((p - 1)! + 1) / p

/-! ## Basic facts -/

/-- **Wilson's theorem**, divisibility form: every prime `p` satisfies `p ∣ (p-1)! + 1`. -/
theorem dvd_factorial_pred_add_one {p : ℕ} (hp : p.Prime) : p ∣ (p - 1)! + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h : (((p - 1)! + 1 : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.wilsons_lemma]
    ring
  exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).1 h

/-- For a prime `p`, the Wilson quotient really is a quotient: `p * W p = (p-1)! + 1`. -/
theorem mul_wilsonQuotient {p : ℕ} (hp : p.Prime) :
    p * wilsonQuotient p = (p - 1)! + 1 :=
  Nat.mul_div_cancel' (dvd_factorial_pred_add_one hp)

/-- Equivalent formulation: a prime is a Wilson prime exactly when it divides its own
Wilson quotient. -/
theorem isWilsonPrime_iff_dvd_wilsonQuotient {p : ℕ} (hp : p.Prime) :
    IsWilsonPrime p ↔ p ∣ wilsonQuotient p := by
  constructor
  · rintro ⟨-, k, hk⟩
    refine ⟨k, ?_⟩
    have h : p * wilsonQuotient p = p * (p * k) := by
      rw [mul_wilsonQuotient hp, hk]; ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos h
  · rintro ⟨k, hk⟩
    refine ⟨hp, ⟨k, ?_⟩⟩
    have h := mul_wilsonQuotient hp
    rw [hk] at h
    rw [← h]; ring

/-- Modular formulation: `p` is a Wilson prime iff `(p-1)! ≡ -1` modulo `p ^ 2`. -/
theorem isWilsonPrime_iff_cast {p : ℕ} :
    IsWilsonPrime p ↔ p.Prime ∧ ((((p - 1)! : ℕ) : ZMod (p ^ 2)) = -1) := by
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    have h0 : (((p - 1)! + 1 : ℕ) : ZMod (p ^ 2)) = 0 :=
      (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).2 h
    push_cast at h0 ⊢
    linear_combination h0
  · intro h
    refine (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).1 ?_
    push_cast at h ⊢
    linear_combination h

/-! ## The known Wilson primes -/

set_option maxRecDepth 10000 in
theorem isWilsonPrime_five : IsWilsonPrime 5 := ⟨by norm_num, by decide⟩

set_option maxRecDepth 10000 in
theorem isWilsonPrime_thirteen : IsWilsonPrime 13 := ⟨by norm_num, by decide⟩

set_option maxRecDepth 10000 in
theorem isWilsonPrime_563 : IsWilsonPrime 563 := ⟨by norm_num, by decide⟩

/-- In particular, at least one Wilson prime exists, so the set is nonempty. -/
theorem wilsonPrimes_nonempty : {p : ℕ | IsWilsonPrime p}.Nonempty :=
  ⟨5, isWilsonPrime_five⟩

/-! ## The infinitude statement

Whether there are infinitely many Wilson primes is an open problem.  What we prove here is
the exact reduction: infinitude of the set of Wilson primes is *equivalent* to the
unboundedness statement "beyond every `N` there is a Wilson prime", and (contrapositive form)
its failure is equivalent to the existence of a bound on all Wilson primes. -/

/-- **Main theorem (conditional reduction).**  If Wilson primes are unbounded — for every `N`
there is a Wilson prime `p > N` — then there are infinitely many Wilson primes. -/
theorem WilsonPrimeInfinitude
    (hUnbounded : ∀ N : ℕ, ∃ p : ℕ, N < p ∧ IsWilsonPrime p) :
    {p : ℕ | IsWilsonPrime p}.Infinite :=
  Set.infinite_of_forall_exists_gt fun N => by
    obtain ⟨p, hNp, hp⟩ := hUnbounded N
    exact ⟨p, hp, hNp⟩

/-- The hypothesis of `WilsonPrimeInfinitude` is not merely sufficient but equivalent:
infinitely many Wilson primes ↔ Wilson primes are unbounded. -/
theorem wilsonPrimes_infinite_iff_unbounded :
    {p : ℕ | IsWilsonPrime p}.Infinite ↔ ∀ N : ℕ, ∃ p : ℕ, N < p ∧ IsWilsonPrime p := by
  refine ⟨fun h N => ?_, WilsonPrimeInfinitude⟩
  obtain ⟨p, hp, hNp⟩ := h.exists_gt N
  exact ⟨p, hNp, hp⟩

/-- Contrapositive form: there are only finitely many Wilson primes exactly when some `N`
bounds them all. -/
theorem wilsonPrimes_finite_iff_bounded :
    {p : ℕ | IsWilsonPrime p}.Finite ↔ ∃ N : ℕ, ∀ p : ℕ, IsWilsonPrime p → p ≤ N := by
  rw [← Set.not_infinite, wilsonPrimes_infinite_iff_unbounded]
  push_neg
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, fun p hp => hN p hp⟩
  · rintro ⟨N, hN⟩
    exact ⟨N, fun p hp => hN p hp⟩

/-- Equivalent reformulation of the conjecture in terms of Wilson quotients: there are
infinitely many Wilson primes iff for every `N` some prime `p > N` divides its Wilson
quotient `((p-1)! + 1) / p`. -/
theorem wilsonPrimes_infinite_iff_wilsonQuotient :
    {p : ℕ | IsWilsonPrime p}.Infinite ↔
      ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ p ∣ wilsonQuotient p := by
  rw [wilsonPrimes_infinite_iff_unbounded]
  constructor
  · intro h N
    obtain ⟨p, hNp, hp⟩ := h N
    exact ⟨p, hNp, hp.1, (isWilsonPrime_iff_dvd_wilsonQuotient hp.1).1 hp⟩
  · intro h N
    obtain ⟨p, hNp, hp, hdvd⟩ := h N
    exact ⟨p, hNp, (isWilsonPrime_iff_dvd_wilsonQuotient hp).2 hdvd⟩

end Brockian.WilsonPrimes

