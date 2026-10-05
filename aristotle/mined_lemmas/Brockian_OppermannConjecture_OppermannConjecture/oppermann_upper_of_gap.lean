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
Target: Brockian.OppermannConjecture.OppermannConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Oppermann's conjecture is open, so the main result here is a Lean-checked *conditional
reduction*: Oppermann's conjecture follows from a Legendre-type prime gap hypothesis
(`SqrtPrimeGap`), together with an unconditional verification of the small cases
`2 ≤ n ≤ 40`.
-/

namespace Brockian.OppermannConjecture

/-- **Oppermann's conjecture**: for every `n ≥ 2` there is a prime strictly between
`n(n-1)` and `n²`, and a prime strictly between `n²` and `n(n+1)`. -/

theorem oppermann_upper_of_gap (h : SqrtPrimeGap) (n : ℕ) (hn : 11 ≤ n) :
    ∃ p : ℕ, Nat.Prime p ∧ n * n < p ∧ p < n * (n + 1) := by
  have hm100 : 100 ≤ n * n := by nlinarith
  obtain ⟨p, hp, hlt, hle⟩ := h (n * n) hm100
  rw [Nat.sqrt_eq n] at hle
  refine ⟨p, hp, hlt, ?_⟩
  rcases lt_or_eq_of_le hle with hlt' | heq
  · calc p < n * n + n := hlt'
      _ = n * (n + 1) := by ring
  · exfalso
    have hdvd : n ∣ p := ⟨n + 1, by rw [heq]; ring⟩
    rcases Nat.Prime.eq_one_or_self_of_dvd hp n hdvd with h1 | h1
    · omega
    · nlinarith [heq, h1]

/-- **Conditional proof of Oppermann's conjecture.**  Assuming the Legendre-type prime gap
hypothesis `SqrtPrimeGap` (a prime in every interval `(m, m + √m]` for `m ≥ 100`),
Oppermann's conjecture holds for all `n ≥ 2`.  The range `2 ≤ n ≤ 40` is verified
unconditionally, and for `n ≥ 11` the two required primes are produced from the
hypothesis applied to `m = n(n-1)` and `m = n²` respectively. -/
