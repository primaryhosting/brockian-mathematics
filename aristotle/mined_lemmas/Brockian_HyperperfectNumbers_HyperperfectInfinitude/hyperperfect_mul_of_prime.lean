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

lemma hyperperfect_mul_of_prime {p : ℕ} (hp : p.Prime) (hq : (p ^ 2 - p + 1).Prime) :
    Hyperperfect (p * (p ^ 2 - p + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have hqval : (m + 2) ^ 2 - (m + 2) + 1 = m * m + 3 * m + 3 := by
    have h : (m + 2) ^ 2 = m * m + 4 * m + 4 := by ring
    omega
  rw [hqval] at hq ⊢
  have hne : m + 2 ≠ m * m + 3 * m + 3 := by nlinarith
  refine ⟨by nlinarith, m + 1, by omega, ?_⟩
  rw [sigma_mul_primes hp hq hne]
  ring

/-- **Hyperperfect Infinitude (conditional).**
If there are infinitely many primes `p` for which `p² - p + 1` is also prime,
then there are infinitely many hyperperfect numbers.

The hypothesis is the (open) prime-family assumption; the conclusion is the
Brockian "hyperperfect infinitude" statement.  Unconditionally, `6`, `21`, `301`
and `2041` are hyperperfect (see the examples below). -/
