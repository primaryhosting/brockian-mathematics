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
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Nat
open ArithmeticFunction

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect when `n = 1 + k * (σ n - n - 1)`.  Written without truncated
subtraction this reads `k * σ n + 1 = (k + 1) * n + k`.  For `k = 1` this is exactly
the condition that `n` is a perfect number. -/

theorem hyperperfect_iff {k n : ℕ} (hn : n + 1 ≤ sigma 1 n) :
    Hyperperfect k n ↔ 1 < n ∧ n = 1 + k * (sigma 1 n - n - 1) := by
  unfold Hyperperfect
  have hexp : (k + 1) * n = k * n + n := by ring
  have key : k * (sigma 1 n - n - 1) = k * sigma 1 n - k * n - k := by
    rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_one]
  have hle : k * n + k ≤ k * sigma 1 n := by
    have h := Nat.mul_le_mul_left k hn
    rw [Nat.mul_add, Nat.mul_one] at h
    exact h
  rw [hexp, key]
  omega

/-! ### Sum-of-divisors computations -/

/-- The sum of divisors of a prime `p` is `p + 1`. -/
