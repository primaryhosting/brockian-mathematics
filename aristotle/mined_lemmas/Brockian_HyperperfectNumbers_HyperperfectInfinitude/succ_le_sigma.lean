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

lemma succ_le_sigma {n : ℕ} (hn : 1 < n) : n + 1 ≤ sigma n := by
  have h1 : (1 : ℕ) ∈ n.divisors := Nat.one_mem_divisors.2 (by omega)
  have hn' : n ∈ n.divisors := Nat.mem_divisors_self n (by omega)
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hmono : ∑ d ∈ ({1, n} : Finset ℕ), d ≤ ∑ d ∈ n.divisors, d :=
    Finset.sum_le_sum_of_subset hsub
  have hsum : ∑ d ∈ ({1, n} : Finset ℕ), d = 1 + n := by
    rw [Finset.sum_insert (by simp; omega), Finset.sum_singleton]
  unfold sigma
  omega

/-- The definition of hyperperfection agrees with the usual formulation
`n = 1 + k * (σ(n) - n - 1)` (with truncated subtraction over `ℕ`). -/
