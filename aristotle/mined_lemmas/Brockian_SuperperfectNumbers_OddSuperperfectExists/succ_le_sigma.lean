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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.SuperperfectNumbers

/-- A natural number `n` is *superperfect* if `σ (σ n) = 2 * n`, where `σ` is the
sum-of-divisors function. -/

theorem succ_le_sigma {N : ℕ} (hN : 1 < N) : N + 1 ≤ σ 1 N := by
  have hN0 : N ≠ 0 := by omega
  have hsub : ({1, N} : Finset ℕ) ⊆ N.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Nat.one_mem_divisors.mpr hN0
    · exact Nat.mem_divisors_self _ hN0
  have key := Finset.sum_le_sum_of_subset (f := fun d => d) hsub
  dsimp only at key
  rw [ArithmeticFunction.sigma_one_apply]
  have hs : ∑ d ∈ ({1, N} : Finset ℕ), d = 1 + N := by
    rw [Finset.sum_insert (by simp; omega), Finset.sum_singleton]
  omega

/-- The sum of divisors of a power of two: `σ (2 ^ k) = 2 ^ (k + 1) - 1`. -/
