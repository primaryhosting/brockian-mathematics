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

open scoped BigOperators
open scoped Nat
open ArithmeticFunction

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect when `n = 1 + k * (σ n - n - 1)`.  Written without truncated
subtraction this reads `k * σ n + 1 = (k + 1) * n + k`.  For `k = 1` this is exactly
the condition that `n` is a perfect number. -/

def HyperperfectAllKStatement : Prop := ∀ k : ℕ, 0 < k → ∃ n : ℕ, Hyperperfect k n

/-- **Conditional reduction of the "hyperperfect numbers exist for every `k`" conjecture.**

No unconditional proof that every `k ≥ 1` admits a `k`-hyperperfect number is given here.
What is proved is a reduction: it suffices to produce, for each `k ≥ 1`, a witness of the shape
`p ^ a * q` (a prime power times a distinct prime) satisfying the hyperperfection equation.
All the explicit examples above are of this shape, and `exists_hyperperfect_of_mem_list`
verifies the hypothesis unconditionally for the listed values of `k`. -/
