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
-/

namespace Brockian.OppermannConjecture

/-- **Oppermann's conjecture**: for every `n > 1` there is a prime strictly between
`n(n-1)` and `n²`, and a prime strictly between `n²` and `n(n+1)`. -/

lemma upper_interval_of_sqrtGap (H : SqrtGapHypothesis) (n : ℕ) (hn : 12 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n * n < p ∧ p < n * (n + 1) := by
  obtain ⟨p, hp, hlt, hub⟩ := H (n * n) (by
    have : 12 * 12 ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
    omega)
  refine ⟨p, hp, hlt, ?_⟩
  rw [Nat.sqrt_eq] at hub
  have : n * (n + 1) = n * n + n := by ring
  omega

/-- **Conditional proof of Oppermann's conjecture.**  Assuming the square-root prime gap
hypothesis (a prime in `(N, N + √N)` for every `N ≥ 118`), Oppermann's conjecture holds:
for every `n > 1` there is a prime strictly between `n(n-1)` and `n²`, and one strictly
between `n²` and `n(n+1)`.  The finitely many remaining cases `2 ≤ n ≤ 11` are verified
directly. -/
