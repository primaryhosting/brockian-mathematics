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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

set_option autoImplicit false

namespace Brockian.QuasiperfectNumbers

/-- A natural number `n` is *quasiperfect* if it is positive and the sum of its divisors
equals `2 * n + 1` (equivalently, the sum of its proper divisors is `n + 1`).
No quasiperfect number is known, and their existence is an open problem. -/

theorem sigma_two_pow_add_one (a : ℕ) : σ 1 (2 ^ a) + 1 = 2 ^ (a + 1) := by
  induction a with
  | zero => simp
  | succ k ih =>
    have h : σ 1 (2 ^ (k + 1)) = σ 1 (2 ^ k) + 2 ^ (k + 1) := by
      rw [sigma_one_apply, sigma_one_apply,
        Nat.sum_divisors_prime_pow Nat.prime_two (f := fun x => x),
        Nat.sum_divisors_prime_pow Nat.prime_two (f := fun x => x),
        Finset.sum_range_succ]
    rw [h]
    ring_nf
    ring_nf at ih
    omega

/-! ### Cattaneo's theorem: a quasiperfect number is an odd square -/

/-- Every quasiperfect number is odd. -/
