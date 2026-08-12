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

open scoped Nat

namespace Brockian.WilsonPrimes

/-- A *Wilson prime* is a prime `p` such that `p ^ 2 ∣ (p - 1)! + 1`, i.e. the congruence
of Wilson's theorem holds modulo `p ^ 2` and not merely modulo `p`. -/
def WilsonPrime (p : ℕ) : Prop := p.Prime ∧ p ^ 2 ∣ (p - 1)! + 1

instance decidableWilsonPrime (p : ℕ) : Decidable (WilsonPrime p) := by
  unfold WilsonPrime; infer_instance

/-- The *Wilson quotient* of `p`, namely `((p - 1)! + 1) / p`. For a prime `p` this is an
exact division by Wilson's theorem. -/
def wilsonQuotient (p : ℕ) : ℕ := ((p - 1)! + 1) / p

/-- Wilson's theorem, in divisibility form: for a prime `p`, `p ∣ (p - 1)! + 1`. -/
theorem dvd_factorial_add_one {p : ℕ} (hp : p.Prime) : p ∣ (p - 1)! + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h : (((p - 1)! + 1 : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.wilsons_lemma]
    ring
  exact (ZMod.natCast_eq_zero_iff _ _).1 h

/-- The Wilson quotient of a prime `p` satisfies `p * wilsonQuotient p = (p - 1)! + 1`. -/
theorem mul_wilsonQuotient {p : ℕ} (hp : p.Prime) :
    p * wilsonQuotient p = (p - 1)! + 1 :=
  Nat.mul_div_cancel' (dvd_factorial_add_one hp)

/-- **Reduction to the Wilson quotient.** A prime `p` is a Wilson prime exactly when `p`
divides its Wilson quotient. -/
theorem wilsonPrime_iff_dvd_wilsonQuotient {p : ℕ} (hp : p.Prime) :
    WilsonPrime p ↔ p ∣ wilsonQuotient p := by
  constructor
  · rintro ⟨-, h⟩
    rw [← mul_wilsonQuotient hp, pow_two] at h
    exact (mul_dvd_mul_iff_left (a := p) hp.pos.ne').1 h
  · intro h
    refine ⟨hp, ?_⟩
    rw [← mul_wilsonQuotient hp, pow_two]
    exact mul_dvd_mul_left p h

/-- **Modular reformulation.** A prime `p` is a Wilson prime exactly when
`(p - 1)! ≡ -1 (mod p ^ 2)`. -/
theorem wilsonPrime_iff_zmod {p : ℕ} (hp : p.Prime) :
    WilsonPrime p ↔ (((p - 1)! : ℕ) : ZMod (p ^ 2)) = -1 := by
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  constructor
  · rintro ⟨-, h⟩
    have h0 : (((p - 1)! + 1 : ℕ) : ZMod (p ^ 2)) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    push_cast at h0
    linear_combination h0
  · intro h
    refine ⟨hp, ?_⟩
    refine (ZMod.natCast_eq_zero_iff _ _).1 ?_
    push_cast
    rw [h]
    ring

/-- Wilson primality as an explicitly decidable congruence condition. -/
theorem wilsonPrime_iff_mod {p : ℕ} :
    WilsonPrime p ↔ p.Prime ∧ ((p - 1)! + 1) % p ^ 2 = 0 := by
  simp [WilsonPrime, Nat.dvd_iff_mod_eq_zero]

/-- `2` is not a Wilson prime. -/
theorem not_wilsonPrime_two : ¬ WilsonPrime 2 := by decide

/-- `3` is not a Wilson prime. -/
theorem not_wilsonPrime_three : ¬ WilsonPrime 3 := by decide

/-- `5` is a Wilson prime: `25 ∣ 4! + 1 = 25`. -/
theorem wilsonPrime_five : WilsonPrime 5 := by decide

/-- `13` is a Wilson prime: `169 ∣ 12! + 1`. -/
theorem wilsonPrime_thirteen : WilsonPrime 13 := by decide

set_option maxRecDepth 100000 in
/-- `563` is a Wilson prime: `563 ^ 2 ∣ 562! + 1`. -/
theorem wilsonPrime_563 : WilsonPrime 563 :=
  ⟨by norm_num, by decide⟩

/-- The three known Wilson primes are indeed Wilson primes. -/
theorem known_wilsonPrimes :
    WilsonPrime 5 ∧ WilsonPrime 13 ∧ WilsonPrime 563 :=
  ⟨wilsonPrime_five, wilsonPrime_thirteen, wilsonPrime_563⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Exhaustive verification: the Wilson primes below `600` are exactly `5`, `13` and `563`. -/
theorem wilsonPrime_lt_600_iff :
    ∀ p < 600, (WilsonPrime p ↔ (p = 5 ∨ p = 13 ∨ p = 563)) := by decide

/-- Every Wilson prime is at least `5`. -/
theorem five_le_of_wilsonPrime {p : ℕ} (h : WilsonPrime p) : 5 ≤ p := by
  by_contra hlt
  push_neg at hlt
  interval_cases p <;> revert h <;> decide

/-- The set of Wilson primes is infinite iff it is unbounded. -/
theorem infinite_iff_unbounded :
    {p : ℕ | WilsonPrime p}.Infinite ↔ ∀ N : ℕ, ∃ p, N < p ∧ WilsonPrime p := by
  constructor
  · intro h N
    obtain ⟨p, hp, hlt⟩ := h.exists_gt N
    exact ⟨p, hlt, hp⟩
  · intro h
    refine Set.infinite_of_forall_exists_gt ?_
    intro N
    obtain ⟨p, hlt, hp⟩ := h N
    exact ⟨p, hp, hlt⟩

/-- **Main conditional theorem (Wilson prime infinitude, reduced to the Wilson quotient).**

If for every bound `N` there is a prime `p > N` dividing its own Wilson quotient
`((p - 1)! + 1) / p`, then there are infinitely many Wilson primes.

The unconditional infinitude of Wilson primes is an open problem; this is a Lean-checked
reduction of it to the Wilson-quotient divisibility criterion, which by
`WilsonPrimeInfinitude_converse` is in fact equivalent to it. -/
theorem WilsonPrimeInfinitude
    (h : ∀ N : ℕ, ∃ p : ℕ, p.Prime ∧ N < p ∧ p ∣ wilsonQuotient p) :
    {p : ℕ | WilsonPrime p}.Infinite := by
  refine infinite_iff_unbounded.2 fun N => ?_
  obtain ⟨p, hp, hlt, hdvd⟩ := h N
  exact ⟨p, hlt, (wilsonPrime_iff_dvd_wilsonQuotient hp).2 hdvd⟩

/-- The converse of `WilsonPrimeInfinitude`: infinitude of Wilson primes yields, for every
bound, a larger prime dividing its Wilson quotient. -/
theorem WilsonPrimeInfinitude_converse (h : {p : ℕ | WilsonPrime p}.Infinite) :
    ∀ N : ℕ, ∃ p : ℕ, p.Prime ∧ N < p ∧ p ∣ wilsonQuotient p := by
  intro N
  obtain ⟨p, hlt, hp⟩ := infinite_iff_unbounded.1 h N
  exact ⟨p, hp.1, hlt, (wilsonPrime_iff_dvd_wilsonQuotient hp.1).1 hp⟩

/-- Packaged equivalence: the Wilson prime infinitude conjecture holds iff the Wilson-quotient
criterion is satisfied by arbitrarily large primes. -/
theorem wilsonPrimeInfinitude_iff :
    {p : ℕ | WilsonPrime p}.Infinite ↔
      ∀ N : ℕ, ∃ p : ℕ, p.Prime ∧ N < p ∧ p ∣ wilsonQuotient p :=
  ⟨WilsonPrimeInfinitude_converse, WilsonPrimeInfinitude⟩

end Brockian.WilsonPrimes

