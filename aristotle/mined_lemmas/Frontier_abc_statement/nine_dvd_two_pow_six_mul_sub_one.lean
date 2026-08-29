/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime divisors. -/

lemma nine_dvd_two_pow_six_mul_sub_one (n : ℕ) : 9 ∣ 2 ^ (6 * n) - 1 := by
  have h63 : 63 ∣ 64 ^ n - 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨k, hk⟩ := ih
      have h1 : 1 ≤ 64 ^ n := Nat.one_le_pow _ _ (by norm_num)
      have h2 : (64 : ℕ) ^ (n + 1) = 64 * 64 ^ n := by ring
      omega
  have h64 : (2 : ℕ) ^ (6 * n) = 64 ^ n := by
    rw [pow_mul]; norm_num
  rw [h64]
  exact dvd_trans (by norm_num) h63

