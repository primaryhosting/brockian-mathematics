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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.QuasiperfectNumbers

open Finset

/-- A natural number `n` is *quasiperfect* if the sum of its divisors equals `2 * n + 1`,
i.e. the sum of its proper divisors is `n + 1`. -/

lemma sigma_two_pow (k : ℕ) :
    ArithmeticFunction.sigma 1 (2 ^ k) + 1 = 2 ^ (k + 1) := by
  have h : ArithmeticFunction.sigma 1 (2 ^ k) = ∑ i ∈ Finset.range (k + 1), 2 ^ i := by
    simp only [ArithmeticFunction.sigma_apply, pow_one]
    exact Nat.sum_divisors_prime_pow Nat.prime_two
  rw [h, sum_two_pow_range]

/-- **Cattaneo-type parity result**: a quasiperfect number is odd. -/
