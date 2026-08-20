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
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Filter UniqueFactorizationMonoid
open scoped Nat

namespace Brockian.BrocardProblem

/-- The `abc` conjecture, stated for natural numbers, using the radical
`UniqueFactorizationMonoid.radical` (the product of the distinct prime factors):
for every `ε > 0` there is a constant `K > 0` such that whenever `a + b = c` with
`a, b` positive and coprime, we have `c ≤ K * rad(a * b * c) ^ (1 + ε)`. -/

lemma radical_factorial_le (n : ℕ) : radical (n !) ≤ 4 ^ n := by
  have hrad : radical (n !) = ∏ p ∈ (n !).primeFactors, p := by
    rw [UniqueFactorizationMonoid.radical,
      UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors]
    rfl
  have hsub : (n !).primeFactors ⊆ (range (n + 1)).filter Nat.Prime := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hpp, hpd, -⟩ := hp
    simp only [mem_filter, mem_range]
    exact ⟨by have := hpp.dvd_factorial.1 hpd; omega, hpp⟩
  calc radical (n !) = ∏ p ∈ (n !).primeFactors, p := hrad
    _ ≤ ∏ p ∈ (range (n + 1)).filter Nat.Prime, p :=
        Finset.prod_le_prod_of_subset_of_one_le' hsub fun i hi _ => (mem_filter.1 hi).2.one_lt.le
    _ = primorial n := rfl
    _ ≤ 4 ^ n := primorial_le_4_pow n

/-- The radical occurring in the `abc` inequality for `1 + n ! = m ^ 2` is at most
`4 ^ n * m`. -/
