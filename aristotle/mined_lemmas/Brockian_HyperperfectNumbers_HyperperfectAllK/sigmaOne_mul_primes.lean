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

namespace Brockian.HyperperfectNumbers

open Finset

/-- `sigmaOne n` is the sum of the divisors of `n`, i.e. `σ₁ n`. -/

lemma sigmaOne_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    sigmaOne (p * q) = (p + 1) * (q + 1) := by
  rw [sigmaOne_mul_coprime ((Nat.coprime_primes hp hq).mpr hne), sigmaOne_prime hp,
    sigmaOne_prime hq]

/-- **Key construction.** If `k ≥ 1` and `k² + 1 = a * b` with `p = k + a` and `q = k + b`
distinct primes, then `p * q` is `k`-hyperperfect.  Indeed, for `n = p * q` the condition
`n = 1 + k(σ(n) - n - 1)` reads `p * q = 1 + k (p + q)`, which is equivalent to
`(p - k)(q - k) = k² + 1`. -/
