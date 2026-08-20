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
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Nat ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace Brockian

namespace BetrothedNumbers

/-- A *betrothed* (quasi-amicable) pair: two distinct positive numbers each of whose
sum of divisors equals `m + n + 1`. -/

theorem odd_sigma_one_iff_factorization {n : ℕ} (hn : n ≠ 0) :
    Odd (σ 1 n) ↔ ∀ p ∈ n.primeFactors, p ≠ 2 → Even (n.factorization p) := by
  rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
  simp only [mul_one, odd_prod_iff]
  refine ⟨fun h p hp hp2 => ?_, fun h p hp => ?_⟩
  · have hodd : Odd p := (Nat.prime_of_mem_primeFactors hp).odd_of_ne_two hp2
    exact (odd_geom_sum_odd hodd).1 (h p hp)
  · rcases eq_or_ne p 2 with rfl | hp2
    · exact odd_geom_sum_two _
    · exact (odd_geom_sum_odd ((Nat.prime_of_mem_primeFactors hp).odd_of_ne_two hp2)).2 (h p hp hp2)

/-- Having all odd primes to even powers means being `2 ^ a` times a square. -/
