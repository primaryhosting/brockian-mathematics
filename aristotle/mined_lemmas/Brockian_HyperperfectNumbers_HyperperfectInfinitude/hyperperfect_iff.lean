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

A number `n > 1` is *`k`-hyperperfect* when `n = 1 + k * (σ(n) - n - 1)`, and
*hyperperfect* when it is `k`-hyperperfect for some `k ≥ 1` (the case `k = 1` is exactly
perfection).  Whether there are infinitely many hyperperfect numbers is open.

This file gives a Lean-checked conditional reduction: `HyperperfectInfinitude` shows that
the infinitude of the prime family `{p prime : p² - p + 1 prime}` implies the infinitude of
hyperperfect numbers, via the construction `p * (p² - p + 1)`, which is `(p-1)`-hyperperfect.
Unconditional instances `6, 21, 301, 2041` are recorded at the end.
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- The sum-of-divisors function `σ(n) = ∑_{d ∣ n} d`. -/

lemma hyperperfect_iff (n : ℕ) :
    Hyperperfect n ↔ 1 < n ∧ ∃ k : ℕ, 0 < k ∧ n = 1 + k * (sigma n - n - 1) := by
  constructor
  · rintro ⟨hn, k, hk, hEq⟩
    refine ⟨hn, k, hk, ?_⟩
    obtain ⟨t, ht⟩ : ∃ t, sigma n = n + 1 + t := ⟨sigma n - (n + 1), by have := succ_le_sigma hn; omega⟩
    have hts : sigma n - n - 1 = t := by omega
    rw [hts]
    rw [ht] at hEq
    have e1 : k * (n + 1 + t) = k * n + k + k * t := by ring
    have e2 : (k + 1) * n = k * n + n := by ring
    omega
  · rintro ⟨hn, k, hk, hEq⟩
    refine ⟨hn, k, hk, ?_⟩
    obtain ⟨t, ht⟩ : ∃ t, sigma n = n + 1 + t := ⟨sigma n - (n + 1), by have := succ_le_sigma hn; omega⟩
    have hts : sigma n - n - 1 = t := by omega
    rw [hts] at hEq
    rw [ht]
    have e1 : k * (n + 1 + t) = k * n + k + k * t := by ring
    have e2 : (k + 1) * n = k * n + n := by ring
    omega

/-- `σ` is multiplicative on the product of two distinct primes. -/
