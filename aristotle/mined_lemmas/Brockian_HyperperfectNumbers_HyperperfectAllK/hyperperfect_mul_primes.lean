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

theorem hyperperfect_mul_primes {k a b p q : ℕ} (hab : a * b = k ^ 2 + 1)
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (hpa : p = k + a) (hqb : q = k + b) :
    Hyperperfect k (p * q) := by
  constructor
  · exact one_lt_mul_of_lt_of_le hp.one_lt hq.one_lt.le
  · have hs : sigmaOne (p * q) = (p + 1) * (q + 1) := sigmaOne_mul_primes hp hq hne
    have hexp : (p + 1) * (q + 1) = p * q + (p + q) + 1 := by ring
    have hsub : sigmaOne (p * q) - p * q - 1 = p + q := by omega
    rw [hsub]
    subst hpa hqb
    have h2 : (k + a) * (k + b) + k ^ 2 = k * (k + a + (k + b)) + a * b := by ring
    rw [hab] at h2
    linarith

/-- For a product of two distinct primes, `k`-hyperperfection is exactly the equation
`p * q = 1 + k * (p + q)`. -/
