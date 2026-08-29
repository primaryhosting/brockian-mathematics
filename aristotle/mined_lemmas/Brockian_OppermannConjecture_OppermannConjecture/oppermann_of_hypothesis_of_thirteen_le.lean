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
# Oppermann Conjecture
Category: Brockian Conjecture
Target: Brockian.OppermannConjecture.OppermannConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Oppermann Conjecture

Category: Brockian Conjecture

Target: `Brockian.OppermannConjecture.OppermannConjecture`

Oppermann's conjecture states that for every `n ≥ 2` there is a prime strictly between
`n(n-1)` and `n²`, and another prime strictly between `n²` and `n(n+1)`.  It is an open
problem (it implies Legendre's and Brocard's conjectures), so what is proved here is a
*conditional reduction* together with an unconditional verification of small cases:

* `ShortIntervalPrimeHypothesis`: for every `m ≥ 117` there is a prime `p > m` with
  `(p - m)² ≤ m`, i.e. `p ≤ m + √m`.  (The threshold `117` is sharp for the small
  exceptions: `m = 3, 7, 8, 13, 23, 24, 31, 113, 114, 115, 116` all fail.)
* `OppermannConjecture`: this hypothesis implies Oppermann's conjecture for all `n ≥ 2`
  (the range `2 ≤ n ≤ 12`, where the hypothesis is not applicable, is verified directly).
* `oppermann_of_le_twelve`: unconditional verification of Oppermann's property for
  `2 ≤ n ≤ 12`.
* `shortIntervalPrime_of_le_three_hundred`: unconditional verification of the hypothesis
  in the range `117 ≤ m ≤ 300`.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace Brockian.OppermannConjecture

/-- Oppermann's property at `n`: there is a prime strictly between `n² - n = n(n-1)` and `n²`,
and a prime strictly between `n²` and `n² + n = n(n+1)`. -/

theorem oppermann_of_hypothesis_of_thirteen_le (H : ShortIntervalPrimeHypothesis) (n : ℕ)
    (hn : 13 ≤ n) : OppermannProperty n := by
  have hle : n ≤ n * n := Nat.le_mul_of_pos_left n (by omega)
  constructor
  · obtain ⟨p, hp, hlt, hsq⟩ := H (n * n - n) (by nlinarith [Nat.sub_add_cancel hle])
    refine ⟨p, hp, hlt, ?_⟩
    by_contra h
    push_neg at h
    have hm : n * n - n + n = n * n := Nat.sub_add_cancel hle
    have h1 : n ≤ p - (n * n - n) := by omega
    have h2 : n * n ≤ (p - (n * n - n)) ^ 2 := by nlinarith
    omega
  · obtain ⟨p, hp, hlt, hsq⟩ := H (n * n) (by nlinarith)
    have hd : p - n * n ≤ n := by nlinarith [Nat.sub_pos_of_lt hlt]
    exact ⟨p, hp, hlt, lt_of_prime_le_mul_succ (by omega) hp (by omega)⟩

/-- **Oppermann's conjecture, conditional on the short-interval prime hypothesis.**

Assuming that every `m ≥ 117` is followed by a prime `p` with `(p - m)² ≤ m` (i.e. `p ≤ m + √m`),
every `n ≥ 2` satisfies Oppermann's property: there is a prime strictly between `n(n-1)` and
`n²`, and a prime strictly between `n²` and `n(n+1)`.  The cases `2 ≤ n ≤ 12`, where the
hypothesis is not applicable, are discharged unconditionally. -/
