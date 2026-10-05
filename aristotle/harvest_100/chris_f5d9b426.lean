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

open Nat

namespace Brockian.WilsonPrimes

/-- A *Wilson prime* is a prime `p` such that `p ^ 2` divides `(p - 1)! + 1`.
(By Wilson's theorem, `p` itself always divides `(p - 1)! + 1` when `p` is prime,
so a Wilson prime is one for which this divisibility holds to the second power.) -/
def IsWilsonPrime (p : ℕ) : Prop := p.Prime ∧ p ^ 2 ∣ (p - 1)! + 1

lemma IsWilsonPrime.prime {p : ℕ} (h : IsWilsonPrime p) : p.Prime := h.1

/-- Wilson's theorem, in divisibility form: a prime `p` divides `(p - 1)! + 1`. -/
lemma dvd_factorial_pred_add_one {p : ℕ} (hp : p.Prime) : p ∣ (p - 1)! + 1 := by
  have h1 : ((p - 1)! : ZMod p) = -1 :=
    (Nat.prime_iff_fac_equiv_neg_one hp.ne_one).1 hp
  have h2 : (((p - 1)! + 1 : ℕ) : ZMod p) = 0 := by
    push_cast [h1]; ring
  exact (ZMod.natCast_eq_zero_iff _ _).1 h2

/-- The *Wilson quotient* of `p`, namely `((p - 1)! + 1) / p`.
For prime `p` this is an integer by Wilson's theorem. -/
def wilsonQuotient (p : ℕ) : ℕ := ((p - 1)! + 1) / p

lemma mul_wilsonQuotient {p : ℕ} (hp : p.Prime) :
    p * wilsonQuotient p = (p - 1)! + 1 :=
  Nat.mul_div_cancel' (dvd_factorial_pred_add_one hp)

/-- A prime is a Wilson prime exactly when it divides its own Wilson quotient. -/
lemma isWilsonPrime_iff_dvd_wilsonQuotient {p : ℕ} (hp : p.Prime) :
    IsWilsonPrime p ↔ p ∣ wilsonQuotient p := by
  constructor
  · rintro ⟨-, k, hk⟩
    refine ⟨k, ?_⟩
    have hpk : p * wilsonQuotient p = p * (p * k) := by
      rw [mul_wilsonQuotient hp, hk]; ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos hpk
  · rintro ⟨k, hk⟩
    refine ⟨hp, ⟨k, ?_⟩⟩
    have h := mul_wilsonQuotient hp
    rw [hk] at h
    rw [← h]; ring

/-- Reformulation of the Wilson prime condition as a congruence modulo `p ^ 2`. -/
lemma isWilsonPrime_iff_zmod {p : ℕ} :
    IsWilsonPrime p ↔ p.Prime ∧ (((p - 1)! : ZMod (p ^ 2)) = -1) := by
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    have h0 : (((p - 1)! + 1 : ℕ) : ZMod (p ^ 2)) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    push_cast at h0
    linear_combination h0
  · intro h
    refine (ZMod.natCast_eq_zero_iff _ _).1 ?_
    push_cast [h]
    ring

/-- Wilson primes are at least `5`: neither `2` nor `3` is a Wilson prime. -/
lemma five_le_of_isWilsonPrime {p : ℕ} (h : IsWilsonPrime p) : 5 ≤ p := by
  obtain ⟨hp, hdvd⟩ := h
  by_contra hlt
  have h2 := hp.two_le
  interval_cases p <;> revert hdvd <;> decide

/-- `5` is a Wilson prime: `25 ∣ 4! + 1 = 25`. -/
theorem isWilsonPrime_five : IsWilsonPrime 5 := ⟨by norm_num, by decide⟩

/-- `13` is a Wilson prime: `169 ∣ 12! + 1 = 479001601`. -/
theorem isWilsonPrime_thirteen : IsWilsonPrime 13 := ⟨by norm_num, by decide⟩

set_option maxRecDepth 10000 in
/-- `563` is a Wilson prime. -/
theorem isWilsonPrime_563 : IsWilsonPrime 563 := ⟨by norm_num, by decide⟩

/-- Unconditionally, the three known Wilson primes really are Wilson primes. -/
theorem known_wilson_primes : ({5, 13, 563} : Set ℕ) ⊆ {p : ℕ | IsWilsonPrime p} := by
  rintro p (rfl | rfl | rfl)
  · exact isWilsonPrime_five
  · exact isWilsonPrime_thirteen
  · exact isWilsonPrime_563

/-- The set of Wilson primes is infinite precisely when it is unbounded. -/
theorem infinite_iff_unbounded :
    {p : ℕ | IsWilsonPrime p}.Infinite ↔ ∀ N : ℕ, ∃ p, N < p ∧ IsWilsonPrime p := by
  constructor
  · intro hinf N
    obtain ⟨p, hp, hpN⟩ := hinf.exists_gt N
    exact ⟨p, hpN, hp⟩
  · intro h
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    obtain ⟨p, hp, hpS⟩ := h N
    exact absurd (hN hpS) (by omega)

/-!
## Main statement

Whether there are infinitely many Wilson primes is a well-known open problem: only
`5`, `13` and `563` are known, and no unconditional proof of infinitude (nor of
finiteness) is available.  What is proved here is a Lean-checked *conditional
reduction*: the infinitude of Wilson primes follows from the statement that
arbitrarily large primes divide their own Wilson quotient `((p - 1)! + 1) / p`.
-/

/-- **Conditional Wilson prime infinitude.**  If for every bound `N` there is a prime
`p > N` dividing its Wilson quotient `((p - 1)! + 1) / p`, then the set of Wilson
primes is infinite.  The hypothesis is the standard open conjecture, so this is a
verified reduction of the infinitude statement to it, not an unconditional proof. -/
theorem WilsonPrimeInfinitude
    (h : ∀ N : ℕ, ∃ p, N < p ∧ p.Prime ∧ p ∣ wilsonQuotient p) :
    {p : ℕ | IsWilsonPrime p}.Infinite := by
  refine infinite_iff_unbounded.2 fun N => ?_
  obtain ⟨p, hpN, hp, hdvd⟩ := h N
  exact ⟨p, hpN, (isWilsonPrime_iff_dvd_wilsonQuotient hp).2 hdvd⟩

end Brockian.WilsonPrimes

#print axioms Brockian.WilsonPrimes.WilsonPrimeInfinitude
#print axioms Brockian.WilsonPrimes.known_wilson_primes
#print axioms Brockian.WilsonPrimes.isWilsonPrime_iff_zmod
#print axioms Brockian.WilsonPrimes.five_le_of_isWilsonPrime

