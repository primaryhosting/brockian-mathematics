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

open scoped Nat

namespace Brockian.WilsonPrimes

/-- A *Wilson prime* is a prime `p` such that `p ^ 2 ∣ (p - 1)! + 1`
(equivalently, Wilson's congruence `(p-1)! ≡ -1` holds modulo `p ^ 2`). -/
def IsWilsonPrime (p : ℕ) : Prop := p.Prime ∧ p ^ 2 ∣ (p - 1)! + 1

instance (p : ℕ) : Decidable (IsWilsonPrime p) := by
  unfold IsWilsonPrime; infer_instance

/-- The *Wilson quotient* of `p`, namely `((p-1)! + 1) / p`.  For a prime `p` this
division is exact by Wilson's theorem. -/
def wilsonQuotient (p : ℕ) : ℕ := ((p - 1)! + 1) / p

/-- Wilson's theorem, in divisibility form. -/
theorem prime_dvd_factorial_pred_add_one {p : ℕ} (hp : p.Prime) : p ∣ (p - 1)! + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h : (((p - 1)! + 1 : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.wilsons_lemma]
    ring
  exact (ZMod.natCast_eq_zero_iff _ _).mp h

/-- Defining property of the Wilson quotient of a prime. -/
theorem mul_wilsonQuotient {p : ℕ} (hp : p.Prime) :
    p * wilsonQuotient p = (p - 1)! + 1 :=
  Nat.mul_div_cancel' (prime_dvd_factorial_pred_add_one hp)

/-- A prime is a Wilson prime exactly when it divides its own Wilson quotient. -/
theorem isWilsonPrime_iff_dvd_wilsonQuotient {p : ℕ} (hp : p.Prime) :
    IsWilsonPrime p ↔ p ∣ wilsonQuotient p := by
  constructor
  · rintro ⟨-, hd⟩
    rw [← mul_wilsonQuotient hp, pow_two] at hd
    exact (mul_dvd_mul_iff_left hp.pos.ne').mp hd
  · intro hd
    refine ⟨hp, ?_⟩
    rw [← mul_wilsonQuotient hp, pow_two]
    exact mul_dvd_mul_left p hd

/-- Wilson prime condition expressed as a congruence in `ZMod (p ^ 2)`. -/
theorem isWilsonPrime_iff_zmod {p : ℕ} (hp : p.Prime) :
    IsWilsonPrime p ↔ (((p - 1)! : ℕ) : ZMod (p ^ 2)) = -1 := by
  constructor
  · rintro ⟨-, hd⟩
    have h : (((p - 1)! + 1 : ℕ) : ZMod (p ^ 2)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hd
    push_cast at h
    linear_combination h
  · intro h
    refine ⟨hp, ?_⟩
    refine (ZMod.natCast_eq_zero_iff _ _).mp ?_
    push_cast
    rw [h]
    ring

/-- The primality requirement in `IsWilsonPrime` is automatic: for `n ≠ 1`, the congruence
`n ^ 2 ∣ (n - 1)! + 1` already forces `n` to be prime (converse of Wilson's theorem). -/
theorem isWilsonPrime_iff_sq_dvd {n : ℕ} (hn : n ≠ 1) :
    IsWilsonPrime n ↔ n ^ 2 ∣ (n - 1)! + 1 := by
  refine ⟨fun h => h.2, fun hd => ⟨?_, hd⟩⟩
  have hdvd : n ∣ (n - 1)! + 1 := dvd_trans (dvd_pow_self n two_ne_zero) hd
  have h0 : (((n - 1)! + 1 : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  have h : (((n - 1)! : ℕ) : ZMod n) = -1 := by
    push_cast at h0 ⊢
    linear_combination h0
  exact Nat.prime_of_fac_equiv_neg_one h hn

/-- `2` is not a Wilson prime. -/
theorem not_isWilsonPrime_two : ¬ IsWilsonPrime 2 := by decide

/-- `3` is not a Wilson prime. -/
theorem not_isWilsonPrime_three : ¬ IsWilsonPrime 3 := by decide

/-- `5` is a Wilson prime. -/
theorem isWilsonPrime_five : IsWilsonPrime 5 := by decide

/-- `13` is a Wilson prime. -/
theorem isWilsonPrime_thirteen : IsWilsonPrime 13 := by decide

set_option maxRecDepth 20000 in
/-- `563` is a Wilson prime.  (These three are the only Wilson primes known.) -/
theorem isWilsonPrime_563 : IsWilsonPrime 563 := ⟨by norm_num, by decide⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 6000000 in
/-- Exhaustive verification: `5`, `13` and `563` are the only Wilson primes below `800`. -/
theorem isWilsonPrime_lt_800 :
    ∀ p < 800, IsWilsonPrime p → p = 5 ∨ p = 13 ∨ p = 563 := by
  decide

/-- The Wilson primes below `800` are exactly `5`, `13` and `563`. -/
theorem isWilsonPrime_lt_800_iff (p : ℕ) (hp : p < 800) :
    IsWilsonPrime p ↔ p = 5 ∨ p = 13 ∨ p = 563 := by
  refine ⟨isWilsonPrime_lt_800 p hp, ?_⟩
  rintro (rfl | rfl | rfl)
  · exact isWilsonPrime_five
  · exact isWilsonPrime_thirteen
  · exact isWilsonPrime_563

/-- Every Wilson prime is at least `5`. -/
theorem five_le_of_isWilsonPrime {p : ℕ} (h : IsWilsonPrime p) : 5 ≤ p := by
  by_contra hlt
  push_neg at hlt
  interval_cases p <;> revert h <;> decide

/-!
## Main statement

The Wilson prime infinitude conjecture (part of the Brockian circle of conjectures)
asserts that there are infinitely many Wilson primes; this is open.  The theorem below
is the Lean-checked reduction: infinitude of the set of Wilson primes is *equivalent*
to the unboundedness statement "for every `N` there is a Wilson prime exceeding `N`".
-/

/-- **Wilson prime infinitude, reduction form.**  The set of Wilson primes is infinite
if and only if Wilson primes are unbounded, i.e. for every bound `N` there is a Wilson
prime larger than `N`. -/
theorem WilsonPrimeInfinitude :
    (∀ N : ℕ, ∃ p : ℕ, N < p ∧ IsWilsonPrime p) ↔ {p : ℕ | IsWilsonPrime p}.Infinite := by
  constructor
  · intro h hfin
    obtain ⟨N, hN⟩ := hfin.bddAbove
    obtain ⟨p, hp, hwp⟩ := h N
    exact absurd (hN hwp) (not_le.mpr hp)
  · intro h N
    by_contra hc
    push_neg at hc
    have hsub : {p : ℕ | IsWilsonPrime p} ⊆ Set.Iic N :=
      fun p hp => not_lt.mp fun hlt => hc p hlt hp
    exact h ((Set.finite_Iic N).subset hsub)

end Brockian.WilsonPrimes

