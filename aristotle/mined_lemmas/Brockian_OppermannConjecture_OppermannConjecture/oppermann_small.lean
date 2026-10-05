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

theorem oppermann_small (n : ℕ) (h2 : 2 ≤ n) (h40 : n ≤ 40) :
    (∃ p : ℕ, Nat.Prime p ∧ n * (n - 1) < p ∧ p < n * n) ∧
    (∃ p : ℕ, Nat.Prime p ∧ n * n < p ∧ p < n * (n + 1)) := by
  have h := oppermann_decide n (Finset.mem_Icc.mpr ⟨h2, h40⟩)
  simp only [Finset.mem_Ioo] at h
  obtain ⟨⟨p, ⟨hp1, hp2⟩, hp⟩, ⟨q, ⟨hq1, hq2⟩, hq⟩⟩ := h
  exact ⟨⟨p, hp, hp1, hp2⟩, ⟨q, hq, hq1, hq2⟩⟩

/-- For `n ≥ 11` the lower Oppermann interval `(n(n-1), n²)` follows from `SqrtPrimeGap`. -/
