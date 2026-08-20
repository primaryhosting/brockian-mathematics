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
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.HyperperfectNumbers

open scoped BigOperators

/-- `n` is `k`-hyperperfect if `n > 1` and `n = 1 + k * (σ(n) - n - 1)`, i.e. `n` is one plus
`k` times the sum of the divisors of `n` other than `1` and `n`. -/

def BrockianFactorizationHypothesis : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ d e : ℕ, d * e = k ^ 2 + 1 ∧ Nat.Prime (k + d) ∧ Nat.Prime (k + e)

/-- **Conditional reduction of the "hyperperfect number for every `k`" conjecture.**
Assuming that for every `k ≥ 1` one can factor `k ^ 2 + 1 = d * e` with `k + d` and `k + e`
prime, every `k ≥ 1` admits a `k`-hyperperfect number. -/
