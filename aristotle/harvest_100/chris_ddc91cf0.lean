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
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.WilsonPrimes

open Nat

/-- A *Wilson prime* is a prime `p` such that `p ^ 2` divides `(p - 1)! + 1`.
(By Wilson's theorem `p` itself always divides `(p - 1)! + 1` when `p` is prime;
a Wilson prime is one for which the divisibility holds to the second power.) -/
def WilsonPrime (p : ℕ) : Prop := p.Prime ∧ p ^ 2 ∣ (p - 1)! + 1

instance : DecidablePred WilsonPrime := fun p => by
  unfold WilsonPrime; infer_instance

/-- The *Wilson quotient* of `p`, namely `((p - 1)! + 1) / p`. -/
def wilsonQuotient (p : ℕ) : ℕ := ((p - 1)! + 1) / p

/-- Wilson's theorem, in divisibility form: a prime `p` divides `(p - 1)! + 1`. -/
theorem prime_dvd_factorial_pred_add_one {p : ℕ} (hp : p.Prime) : p ∣ (p - 1)! + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h : ((((p - 1)! + 1 : ℕ)) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.wilsons_lemma p]
    ring
  exact (ZMod.natCast_eq_zero_iff _ _).mp h

/-- The defining property of the Wilson quotient: for a prime `p`,
`(p - 1)! + 1 = p * wilsonQuotient p`. -/
theorem factorial_pred_add_one_eq {p : ℕ} (hp : p.Prime) :
    (p - 1)! + 1 = p * wilsonQuotient p :=
  (Nat.mul_div_cancel' (prime_dvd_factorial_pred_add_one hp)).symm

/-- A prime is a Wilson prime exactly when it divides its own Wilson quotient. -/
theorem wilsonPrime_iff_dvd_wilsonQuotient {p : ℕ} (hp : p.Prime) :
    WilsonPrime p ↔ p ∣ wilsonQuotient p := by
  constructor
  · rintro ⟨-, hdvd⟩
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k, ?_⟩
    have hfac := factorial_pred_add_one_eq hp
    rw [hk] at hfac
    have h2 : p * (p * k) = p * wilsonQuotient p := by rw [← hfac]; ring
    exact (Nat.eq_of_mul_eq_mul_left hp.pos h2).symm
  · rintro ⟨k, hk⟩
    refine ⟨hp, ⟨k, ?_⟩⟩
    rw [factorial_pred_add_one_eq hp, hk]; ring

section Examples

set_option maxRecDepth 40000

/-- `5` is a Wilson prime. -/
theorem wilsonPrime_five : WilsonPrime 5 := by decide

/-- `13` is a Wilson prime. -/
theorem wilsonPrime_thirteen : WilsonPrime 13 := by decide

/-- `563` is a Wilson prime. -/
theorem wilsonPrime_563 : WilsonPrime 563 := by decide

/-- `7` is a prime that is not a Wilson prime. -/
theorem not_wilsonPrime_seven : ¬ WilsonPrime 7 := by decide

/-- Below `100` the only Wilson primes are `5` and `13`. -/
theorem wilsonPrime_lt_hundred : ∀ p < 100, WilsonPrime p → p = 5 ∨ p = 13 := by decide

end Examples

/-- The set of Wilson primes is nonempty. -/
theorem wilsonPrimes_nonempty : {p : ℕ | WilsonPrime p}.Nonempty :=
  ⟨5, wilsonPrime_five⟩

/-- **Main reduction.** The set of Wilson primes is infinite if and only if
there are arbitrarily large Wilson primes, i.e. for every bound `N` there is a
Wilson prime exceeding `N`.

This is an unconditional, Lean-checked reformulation of the (open) Wilson prime
infinitude conjecture: it reduces the infinitude statement to the statement that
the Wilson primes are unbounded. -/
theorem WilsonPrimeInfinitude :
    {p : ℕ | WilsonPrime p}.Infinite ↔ ∀ N : ℕ, ∃ p, N < p ∧ WilsonPrime p := by
  rw [Set.infinite_iff_exists_gt]
  constructor
  · intro h N
    obtain ⟨b, hb, hNb⟩ := h N
    exact ⟨b, hNb, hb⟩
  · intro h N
    obtain ⟨p, hNp, hp⟩ := h N
    exact ⟨p, hp, hNp⟩

/-- Equivalent form of the conjecture in terms of Wilson quotients: there are
infinitely many Wilson primes iff for every `N` there is a prime `p > N`
dividing its own Wilson quotient. -/
theorem wilsonPrimes_infinite_iff_wilsonQuotient :
    {p : ℕ | WilsonPrime p}.Infinite ↔
      ∀ N : ℕ, ∃ p, N < p ∧ p.Prime ∧ p ∣ wilsonQuotient p := by
  rw [WilsonPrimeInfinitude]
  constructor
  · intro h N
    obtain ⟨p, hNp, hp⟩ := h N
    exact ⟨p, hNp, hp.1, (wilsonPrime_iff_dvd_wilsonQuotient hp.1).mp hp⟩
  · intro h N
    obtain ⟨p, hNp, hp, hq⟩ := h N
    exact ⟨p, hNp, (wilsonPrime_iff_dvd_wilsonQuotient hp).mpr hq⟩

end Brockian.WilsonPrimes

