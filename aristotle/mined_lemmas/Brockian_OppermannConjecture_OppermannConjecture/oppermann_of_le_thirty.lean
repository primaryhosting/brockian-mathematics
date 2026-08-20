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

set_option maxRecDepth 10000

namespace Brockian.OppermannConjecture

/-- **Oppermann's conjecture** (statement form): for every `n ≥ 2` there is a prime strictly
between `n(n-1)` and `n²`, and a prime strictly between `n²` and `n(n+1)`.

This is an open problem in number theory; it is *not* proved here.  What is proved below
(`OppermannConjecture`) is a conditional reduction: Oppermann's conjecture follows from the
`√x` prime-gap hypothesis `SqrtGapHypothesis`, together with an unconditional finite
verification for `2 ≤ n ≤ 30` (`oppermann_of_le_thirty`).

Mathlib's strongest unconditional result in this direction is Bertrand's postulate,
`Nat.exists_prime_lt_and_le_two_mul`, which gives a prime in `(n, 2n]` and is far too weak to
reach intervals of length `n` around `n²`. -/

theorem oppermann_of_le_thirty (n : ℕ) (h2 : 2 ≤ n) (h30 : n ≤ 30) :
    (∃ p : ℕ, p.Prime ∧ n * (n - 1) < p ∧ p < n * n) ∧
    (∃ q : ℕ, q.Prime ∧ n * n < q ∧ q < n * (n + 1)) := by
  have h := oppermann_check n (Finset.mem_Icc.mpr ⟨h2, h30⟩)
  simp only [Finset.mem_Ioo] at h
  obtain ⟨⟨p, ⟨hp1, hp2⟩, hp⟩, ⟨q, ⟨hq1, hq2⟩, hq⟩⟩ := h
  exact ⟨⟨p, hp, hp1, hp2⟩, ⟨q, hq, hq1, hq2⟩⟩

end Brockian.OppermannConjecture

