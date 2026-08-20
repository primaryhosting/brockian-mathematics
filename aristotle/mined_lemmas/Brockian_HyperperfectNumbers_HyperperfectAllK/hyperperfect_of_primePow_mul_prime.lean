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

theorem hyperperfect_of_primePow_mul_prime {k p t q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (heq : (q : ℤ) * ((k + 1) * (p : ℤ) ^ t - k * (sigmaPrimePow p t : ℤ))
        = k * (sigmaPrimePow p t : ℤ) - k + 1) :
    Hyperperfect k (p ^ t * q) :=
  (hyperperfect_primePow_mul_prime_iff hp hq hpq).mpr heq

/-- The semiprime case `t = 1`: `p * q` is `k`-hyperperfect iff `(p - k) * (q - k) = k ^ 2 + 1`. -/
