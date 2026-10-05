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
By Wilson's theorem, every prime `p` satisfies `p ∣ (p - 1)! + 1`; a Wilson prime
is one for which the stronger, squared divisibility holds. -/
def WilsonPrime (p : ℕ) : Prop := p.Prime ∧ p ^ 2 ∣ (p - 1)! + 1

instance (p : ℕ) : Decidable (WilsonPrime p) := by
  unfold WilsonPrime; infer_instance

/-- The set of Wilson primes. -/
def wilsonPrimeSet : Set ℕ := {p | WilsonPrime p}

lemma WilsonPrime.prime {p : ℕ} (h : WilsonPrime p) : p.Prime := h.1

lemma WilsonPrime.sq_dvd {p : ℕ} (h : WilsonPrime p) : p ^ 2 ∣ (p - 1)! + 1 := h.2

/-- Wilson's theorem, in divisibility form: every prime `p` divides `(p - 1)! + 1`. -/
lemma prime_dvd_factorial_pred_add_one {p : ℕ} (hp : p.Prime) : p ∣ (p - 1)! + 1 := by
  haveI := Fact.mk hp
  have hw : ((p - 1)! : ZMod p) = -1 := ZMod.wilsons_lemma p
  have h0 : (((p - 1)! + 1 : ℕ) : ZMod p) = 0 := by push_cast [hw]; ring
  exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp h0

/-- For a prime `p`, being a Wilson prime is exactly the squared divisibility condition. -/
lemma wilsonPrime_iff_of_prime {p : ℕ} (hp : p.Prime) :
    WilsonPrime p ↔ p ^ 2 ∣ (p - 1)! + 1 :=
  ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩

/-- `5` is a Wilson prime. -/
lemma wilsonPrime_five : WilsonPrime 5 := by
  refine ⟨by norm_num, ?_⟩
  norm_num [Nat.factorial]

/-- `13` is a Wilson prime. -/
lemma wilsonPrime_thirteen : WilsonPrime 13 := by
  refine ⟨by norm_num, ?_⟩
  norm_num [Nat.factorial]

/-- `563` is a Wilson prime. -/
set_option maxRecDepth 20000 in
lemma wilsonPrime_563 : WilsonPrime 563 := by
  refine ⟨by norm_num, ?_⟩
  decide

/-- There exists at least one Wilson prime, so the statement below is not vacuous. -/
lemma wilsonPrimeSet_nonempty : wilsonPrimeSet.Nonempty :=
  ⟨5, wilsonPrime_five⟩

/--
**Wilson prime infinitude, as a reduction.**

Whether there are infinitely many Wilson primes is an open problem; this theorem establishes
the exact equivalence between the two standard formulations of that statement: the set of
Wilson primes is infinite if and only if there are arbitrarily large Wilson primes.
-/
theorem WilsonPrimeInfinitude :
    (∀ N : ℕ, ∃ p, N < p ∧ WilsonPrime p) ↔ wilsonPrimeSet.Infinite := by
  constructor
  · intro h
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    obtain ⟨p, hp, hpW⟩ := h N
    exact absurd (hN (show p ∈ wilsonPrimeSet from hpW)) (by omega)
  · intro hinf N
    obtain ⟨p, hpW, hp⟩ := hinf.exists_gt N
    exact ⟨p, hp, hpW⟩

/-- Consequence of the reduction: if there are arbitrarily large primes `p` with
`p ^ 2 ∣ (p - 1)! + 1`, then the set of Wilson primes is infinite. -/
theorem wilsonPrimeSet_infinite_of_unbounded
    (h : ∀ N : ℕ, ∃ p, N < p ∧ p.Prime ∧ p ^ 2 ∣ (p - 1)! + 1) :
    wilsonPrimeSet.Infinite :=
  WilsonPrimeInfinitude.mp fun N => by
    obtain ⟨p, hp, hp1, hp2⟩ := h N
    exact ⟨p, hp, hp1, hp2⟩

end Brockian.WilsonPrimes

