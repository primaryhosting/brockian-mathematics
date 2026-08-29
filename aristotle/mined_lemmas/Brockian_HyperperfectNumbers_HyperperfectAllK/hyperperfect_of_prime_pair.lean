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

theorem hyperperfect_of_prime_pair {k : ℕ} (hk : 0 < k) (h1 : (k + 1).Prime)
    (h2 : (k ^ 2 + k + 1).Prime) :
    Hyperperfect k ((k + 1) * (k ^ 2 + k + 1)) := by
  have h : (k + (k ^ 2 + 1)) = k ^ 2 + k + 1 := by ring
  have := hyperperfect_mul_of_primes (k := k) (a := 1) (b := k ^ 2 + 1) (by ring)
    (by simpa using h1) (by rw [h]; exact h2) (by nlinarith)
  simpa [h] using this

/-! ### Explicit hyperperfect numbers -/

