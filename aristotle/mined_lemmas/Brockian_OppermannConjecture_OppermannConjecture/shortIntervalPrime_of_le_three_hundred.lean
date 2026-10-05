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

theorem shortIntervalPrime_of_le_three_hundred (m : ℕ) (h1 : 117 ≤ m) (h2 : m ≤ 300) :
    ∃ p, Nat.Prime p ∧ m < p ∧ (p - m) ^ 2 ≤ m := by
  have key : ∀ k ∈ Finset.Icc 117 300,
      ∃ p ∈ Finset.Ioo k (k + 40), Nat.Prime p ∧ (p - k) ^ 2 ≤ k := by decide
  obtain ⟨p, hmem, hp, hsq⟩ := key m (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  exact ⟨p, hp, (Finset.mem_Ioo.mp hmem).1, hsq⟩

/-- `n(n+1)` is composite for `n ≥ 2`, so a prime `p ≤ n² + n` is in fact `< n² + n`. -/
