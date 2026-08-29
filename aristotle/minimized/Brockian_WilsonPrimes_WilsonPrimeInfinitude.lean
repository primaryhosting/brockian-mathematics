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
