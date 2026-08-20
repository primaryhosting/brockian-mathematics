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

namespace Brockian
namespace QuasiperfectNumbers

open Finset

/-- A positive natural number `n` is *quasiperfect* if the sum of all of its divisors is
`2 * n + 1`, equivalently if the sum of its proper divisors is `n + 1`.

Whether a quasiperfect number exists is a longstanding open problem; no example is known,
and none can be small (see `no_quasiperfect_lt_500`). -/

theorem odd_sum_divisors_prime_pow_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (e : ℕ) :
    Odd (∑ d ∈ (p ^ e).divisors, d) ↔ Even e := by
  rw [Nat.sum_divisors_prime_pow hp (f := fun d => d)]
  exact odd_geomSum_iff (hp.odd_of_ne_two hp2) e

/-- The sum-of-divisors function is multiplicative. -/
