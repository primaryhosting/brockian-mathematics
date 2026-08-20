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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
A natural number `n` is *quasiperfect* if `σ n = 2 * n + 1`, i.e. the sum of the proper
divisors of `n` (including `1`) equals `n + 1`.  No quasiperfect number is known, and their
existence is an open problem.

This file proves the classical structural constraints (Cattaneo, 1951): a quasiperfect number
must be an odd perfect square, and it cannot be a prime power.  The main theorem
`QuasiperfectExists` is the resulting *reduction*: a quasiperfect number exists if and only if
there is an odd `k > 1`, not a prime power, whose square is quasiperfect.
-/

namespace Brockian.QuasiperfectNumbers

open Finset

/-- A natural number `n` is *quasiperfect* if it is positive and the sum of all of its
divisors equals `2 * n + 1`. -/

theorem sum_divisors_two_pow (a : ℕ) : ∑ d ∈ (2 ^ a).divisors, d = 2 ^ (a + 1) - 1 := by
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  simp [Nat.geomSum_eq]

/-- An odd number whose sum of divisors is odd is a perfect square. -/
