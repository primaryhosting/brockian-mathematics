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

theorem isHyperperfect_of_prime_prime {k : ℕ} (hk : 1 ≤ k) (hp : Nat.Prime (k + 1))
    (hq : Nat.Prime (k ^ 2 + k + 1)) :
    IsHyperperfect k ((k + 1) * (k ^ 2 + k + 1)) := by
  have h : k + (k ^ 2 + 1) = k ^ 2 + k + 1 := by ring
  have := isHyperperfect_of_factorization (d := 1) (e := k ^ 2 + 1) hk (by ring)
    (by simpa using hp) (by rw [h]; exact hq)
  simpa [h] using this

/-! ### A second family: `p ^ 2 * q` -/

/-- The sum of divisors of `p ^ 2 * q` for distinct primes `p`, `q`. -/
