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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- The sum of all divisors of `n`, i.e. `σ₁ n`. -/

theorem restrictedSum_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    restrictedSum (p * q) = p + q := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  have hs : sigmaSum (p * q) = (1 + p) * (1 + q) := by
    rw [sigmaSum_mul_of_coprime hcop, sigmaSum_prime hp, sigmaSum_prime hq]
  have hexp : (1 + p) * (1 + q) = (p * q + 1) + (p + q) := by ring
  rw [restrictedSum, hs]
  omega

/-- **The Minoli–Bear family.** If `p` and `q = p² - p + 1` are primes, then `p * q` is
`(p - 1)`-hyperperfect. -/
