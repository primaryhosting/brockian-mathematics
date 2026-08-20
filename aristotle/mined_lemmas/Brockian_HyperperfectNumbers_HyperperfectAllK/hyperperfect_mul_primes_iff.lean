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

theorem hyperperfect_mul_primes_iff {k p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    Hyperperfect k (p * q) ↔ p * q = 1 + k * (p + q) := by
  have hs : sigmaOne (p * q) = (p + 1) * (q + 1) := sigmaOne_mul_primes hp hq hne
  have hexp : (p + 1) * (q + 1) = p * q + (p + q) + 1 := by ring
  have hsub : sigmaOne (p * q) - p * q - 1 = p + q := by omega
  constructor
  · rintro ⟨-, h⟩
    rwa [hsub] at h
  · intro h
    exact ⟨one_lt_mul_of_lt_of_le hp.one_lt hq.one_lt.le, by rw [hsub]; exact h⟩

/-- **Brockian conjecture: hyperperfect numbers for all `k` (conditional form).**

For every `k ≥ 1` for which the two numbers `k + 1` and `k² + k + 1` are prime, there is a
`k`-hyperperfect number, namely `n = (k + 1)(k² + k + 1)`.

This is the standard reduction of the (open) statement "for every `k ≥ 1` there is a
`k`-hyperperfect number" to a primality hypothesis: the general solvability of
`p * q = 1 + k (p + q)` in primes, equivalently `(p - k)(q - k) = k² + 1`, is not known
for all `k`, so we record the conditional statement together with the explicit witness. -/
