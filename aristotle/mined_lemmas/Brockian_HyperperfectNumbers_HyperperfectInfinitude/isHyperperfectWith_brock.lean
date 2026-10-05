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

theorem isHyperperfectWith_brock {p : ℕ} (hp : p.Prime) (hq : (brockPartner p).Prime) :
    IsHyperperfectWith (p - 1) (p * brockPartner p) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hp.two_le
  have hqval : brockPartner (2 + m) = m * m + 3 * m + 3 := by
    have h : (2 + m) * (2 + m) = (m * m + 3 * m + 3) + (2 + m) - 1 := by ring_nf; omega
    simp only [brockPartner]
    omega
  have hne : (2 + m) ≠ brockPartner (2 + m) := by rw [hqval]; omega
  refine ⟨by omega, ?_, ?_⟩
  · have h1 : 1 ≤ brockPartner (2 + m) := by omega
    calc 2 ≤ 2 + m := by omega
    _ = (2 + m) * 1 := by ring
    _ ≤ (2 + m) * brockPartner (2 + m) := Nat.mul_le_mul_left _ h1
  · rw [sigma1_mul_of_primes hp hq hne, hqval]
    have hk : 2 + m - 1 = 1 + m := by omega
    rw [hk]
    ring

/-- If `p` and `p² - p + 1` are both prime then `p * (p² - p + 1)` is hyperperfect. -/
