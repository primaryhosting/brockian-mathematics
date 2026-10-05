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

theorem add_add_one_le_sigma_of_dvd {N a : ℕ} (ha : a ∣ N) (h1 : 1 < a) (h2 : a < N) :
    N + a + 1 ≤ σ 1 N := by
  have hN : N ≠ 0 := by omega
  have hsub : ({1, a, N} : Finset ℕ) ⊆ N.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Nat.one_mem_divisors.mpr hN
    · exact Nat.mem_divisors.mpr ⟨ha, hN⟩
    · exact Nat.mem_divisors_self _ hN
  have key := Finset.sum_le_sum_of_subset (f := fun d => d) hsub
  dsimp only at key
  rw [ArithmeticFunction.sigma_one_apply]
  have hs : ∑ d ∈ ({1, a, N} : Finset ℕ), d = 1 + a + N := by
    rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
      Finset.sum_singleton]
    ring
  omega

/-- For `N > 1` we have `σ N ≥ N + 1`. -/
