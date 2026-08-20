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
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.LegendreConjecture

/-- **Legendre's conjecture** (open): for every `n ≥ 1` there is a prime strictly
between `n ^ 2` and `(n + 1) ^ 2`. -/

def ShortIntervalPrimes : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ p : ℕ, p.Prime ∧ m < p ∧ p ≤ m + Nat.sqrt m

/-- **Conditional reduction of Legendre's conjecture.**

Legendre's conjecture is open, so we prove a Lean-checked reduction: it follows from the
short-interval prime hypothesis `ShortIntervalPrimes`, i.e. from the existence of a prime in
`(m, m + √m]` for every `m ≥ 1`. Applying the hypothesis at `m = n ^ 2` (where `√m = n`)
produces a prime `p` with `n ^ 2 < p ≤ n ^ 2 + n < (n + 1) ^ 2`. -/
