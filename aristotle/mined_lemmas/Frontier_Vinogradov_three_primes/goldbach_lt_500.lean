import Mathlib

/-!
# Vinogradov Three Primes
Category: Frontier — Prime Numbers
Target: Frontier.Vinogradov_three_primes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- `IsSumOfThreePrimes n` says that `n` can be written as a sum of three (not necessarily
distinct) prime numbers. -/

theorem goldbach_lt_500 :
    ∀ m < 500, 4 ≤ m → m % 2 = 0 → ∃ p < m, Nat.Prime p ∧ Nat.Prime (m - p) := by
  decide

/-- Unconditional base case: every odd number `n` with `9 ≤ n ≤ 502` is a sum of three primes. -/
