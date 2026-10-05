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

/-!
## Overview

A natural number `n` is *`k`-hyperperfect* (for `k ≥ 1`) when

  `n = 1 + k * (σ n - n - 1)`,

where `σ n` is the sum of the divisors of `n`; equivalently (avoiding truncated
subtraction) `n + k * (n + 1) = 1 + k * σ n`.  The `1`-hyperperfect numbers are
exactly the perfect numbers.  It is an open conjecture that there are infinitely
many hyperperfect numbers.

This file gives a Lean-checked **conditional reduction** of that conjecture to a
Bunyakovsky-type prime hypothesis: if there are infinitely many primes `p` for
which `p² - p + 1` is also prime, then there are infinitely many hyperperfect
numbers.  The construction is explicit: for such a `p`, the number
`n = p * (p² - p + 1)` is `(p - 1)`-hyperperfect (e.g. `p = 2` gives the perfect
number `6`, `p = 3` gives `21`, `p = 7` gives `301`).
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- The sum-of-divisors function `σ`. -/

theorem isHyperperfectWith_one_euclid {k : ℕ} (hk : 1 ≤ k) (hq : (2 ^ (k + 1) - 1).Prime) :
    IsHyperperfectWith 1 (2 ^ k * (2 ^ (k + 1) - 1)) := by
  have h4 : 4 ≤ 2 ^ (k + 1) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpk : 2 ≤ 2 ^ k := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hdouble : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
  refine ⟨le_refl _, ?_, ?_⟩
  · calc (2 : ℕ) ≤ 2 ^ k := hpk
    _ = 2 ^ k * 1 := by ring
    _ ≤ 2 ^ k * (2 ^ (k + 1) - 1) := Nat.mul_le_mul_left _ (by omega)
  · rw [sigma1_euclid hq]
    set B := 2 ^ (k + 1) - 1 with hB
    have hBv : 2 * 2 ^ k = B + 1 := by omega
    have e1 : 2 * (2 ^ k * B) = (B + 1) * B := by rw [← Nat.mul_assoc, hBv]
    have e2 : B * (1 + B) = (B + 1) * B := by ring
    omega

/-- The hypothesis that there are infinitely many Mersenne primes. -/
