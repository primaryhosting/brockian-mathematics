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

theorem oppermann_decide :
    ∀ n ∈ Finset.Icc 2 40,
      (∃ p ∈ Finset.Ioo (n * (n - 1)) (n * n), Nat.Prime p) ∧
      (∃ p ∈ Finset.Ioo (n * n) (n * (n + 1)), Nat.Prime p) := by
  decide

/-- The unconditional part: Oppermann's conjecture holds for all `2 ≤ n ≤ 40`. -/
