import Brockian.LandauNSquaredPlusOne

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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.LandauNSquaredPlusOne

open Set

/-- The set of primes of the form `n ^ 2 + 1` (the "Landau primes"). -/

theorem even_of_landauPrime {p : ℕ} (hp : p ∈ LandauPrimes) (hne : p ≠ 2) :
    ∃ m : ℕ, 0 < m ∧ p = (2 * m) ^ 2 + 1 := by
  obtain ⟨hpp, n, rfl⟩ := hp
  have hn2 : n % 2 = 0 := by
    by_contra hodd
    obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    have hdvd : 2 ∣ n ^ 2 + 1 := ⟨2 * k * k + 2 * k + 1, by subst hk; ring⟩
    exact hne ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).1 hdvd).symm
  have hn0 : n ≠ 0 := by
    rintro rfl
    norm_num at hpp
  refine ⟨n / 2, by omega, ?_⟩
  have h : 2 * (n / 2) = n := by omega
  rw [h]

/-- An odd prime dividing some `n ^ 2 + 1` is congruent to `1` modulo `4`. -/
