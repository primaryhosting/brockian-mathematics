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

