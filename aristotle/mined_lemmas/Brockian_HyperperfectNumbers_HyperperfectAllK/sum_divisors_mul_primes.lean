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

/-- `Hyperperfect k n` says that `n` is a *`k`-hyperperfect number*, i.e. `n > 1` and
`n = 1 + k * (σ(n) - n - 1)`, where `σ(n) = ∑ d ∣ n, d`.

The defining equation is written in the subtraction-free form
`(k + 1) * n + k = k * σ(n) + 1`, which over the integers is equivalent to
`n = 1 + k * (σ n - n - 1)`. -/

theorem sum_divisors_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∑ d ∈ (p * q).divisors, d = (1 + p) * (1 + q) := by
  rw [Nat.Coprime.sum_divisors_mul ((Nat.coprime_primes hp hq).2 hpq),
    hp.divisors, hq.divisors, Finset.sum_pair hp.one_lt.ne, Finset.sum_pair hq.one_lt.ne]

/-- **Characterisation of hyperperfect semiprimes.** For distinct primes `p`, `q`, the number
`p * q` is `k`-hyperperfect exactly when `p * q = k * p + k * q + 1`, i.e. (over `ℤ`)
`(p - k) * (q - k) = k ^ 2 + 1`. -/
