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
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.GilbreathConjecture

/-! ## Primes -/

/-- `n` is prime: it is at least `2` and has no divisor `d` with `2 ≤ d < n`. -/

theorem isPrimeNat_iff_prime {n : ℕ} : IsPrimeNat n ↔ Nat.Prime n := by
  rw [Nat.prime_def_lt]
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm hmn => ?_⟩
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m
      · exact absurd (Nat.eq_zero_of_zero_dvd hmn) (by omega)
      · rfl
    · exact absurd hmn (h m hm hm2)
  · rintro ⟨h2, h⟩
    exact ⟨h2, fun d hd hd2 hdvd => by simp [h d hd hdvd] at hd2⟩

/-- `Nat.nth Nat.Prime` is an increasing enumeration of the primes. -/
