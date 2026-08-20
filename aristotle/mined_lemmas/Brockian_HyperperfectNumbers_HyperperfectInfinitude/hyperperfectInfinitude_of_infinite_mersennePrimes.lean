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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- `sigmaOne n` is the sum of all divisors of `n`, usually written `σ₁ (n)`. -/

theorem hyperperfectInfinitude_of_infinite_mersennePrimes
    (H : {p : ℕ | (2 ^ p - 1).Prime}.Infinite) : Hyperperfect.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hp, hpN⟩ := H.exists_gt (N + 2)
  simp only [Set.mem_setOf_eq] at hp
  have hp2 : 2 ≤ p := by
    by_contra h
    push_neg at h
    interval_cases p <;> norm_num at hp
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  have hone : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have hqe : (2 ^ (k + 1) - 1) + 1 = 2 ^ (k + 1) := by omega
  refine ⟨2 ^ k * (2 ^ (k + 1) - 1), ⟨1, isHyperperfect_one_of_mersenne (by omega) hp hqe⟩, ?_⟩
  have hq2 : 2 ≤ 2 ^ (k + 1) - 1 := hp.two_le
  have hlt : k < 2 ^ k := Nat.lt_two_pow_self
  calc N < k := by omega
    _ < 2 ^ k := hlt
    _ = 2 ^ k * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ k * (2 ^ (k + 1) - 1) := Nat.mul_le_mul_left _ (by omega)

/-- **Conditional infinitude of hyperperfect numbers.**  If there are infinitely many primes `p`
for which `p² - p + 1` is also prime, then there are infinitely many hyperperfect numbers. -/
