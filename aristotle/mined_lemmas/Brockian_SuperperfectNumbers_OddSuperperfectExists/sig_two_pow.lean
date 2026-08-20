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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian
namespace SuperperfectNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/

lemma sig_two_pow (a : ℕ) : sig (2 ^ a) = 2 ^ (a + 1) - 1 := by
  rw [sig_eq_sum, Nat.sum_divisors_prime_pow Nat.prime_two]
  induction a with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, ih]
    have : 1 ≤ 2 ^ (b + 1) := Nat.one_le_two_pow
    ring_nf
    omega

