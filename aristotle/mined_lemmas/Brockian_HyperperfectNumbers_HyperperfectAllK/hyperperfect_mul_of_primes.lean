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

theorem hyperperfect_mul_of_primes {k a b : ℕ} (hab : a * b = k ^ 2 + 1)
    (hp : (k + a).Prime) (hq : (k + b).Prime) (hne : a ≠ b) :
    Hyperperfect k ((k + a) * (k + b)) := by
  have hpq : k + a ≠ k + b := by omega
  have hwit : Witness k (k + a) 1 (k + b) := by
    refine ⟨hp, hq, hpq, le_refl 1, ?_⟩
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
    nlinarith [hab]
  have := hyperperfect_of_witness hwit
  simpa using this

/-- **Characterisation in the semiprime case.**  For distinct primes `p` and `q`, the number
`p * q` is `k`-hyperperfect exactly when `k * p + k * q + 1 = p * q`, i.e. (over `ℤ`)
when `(p - k) * (q - k) = k ^ 2 + 1`. -/
