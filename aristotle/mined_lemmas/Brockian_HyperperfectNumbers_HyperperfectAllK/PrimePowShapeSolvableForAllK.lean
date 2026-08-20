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

import Mathlib
/-!
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect when `n = 1 + k * (σ n - n - 1)`, i.e. `n` is one more than
`k` times the sum of its proper divisors other than `1`.  For `k = 1` this is exactly the
condition of being a perfect number. -/

def PrimePowShapeSolvableForAllK : Prop :=
  ∀ k : ℕ, 0 < k → ∃ p t q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧
    (q : ℤ) * ((k + 1) * (p : ℤ) ^ t - k * (sigmaPrimePow p t : ℤ))
      = k * (sigmaPrimePow p t : ℤ) - k + 1

/-- **Conditional reduction of the "hyperperfect numbers for all `k`" conjecture.**
If for every `k ≥ 1` the prime-power/prime Diophantine equation
`q * ((k+1) * p ^ t - k * S) = k * S - k + 1` (with `S = 1 + p + ⋯ + p ^ t`) is solvable in
distinct primes `p, q`, then a `k`-hyperperfect number exists for every `k ≥ 1`. -/
