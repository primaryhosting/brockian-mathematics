/-
# Vinogradov Three Primes
Category: Frontier — Prime Numbers
Target: Frontier.Vinogradov_three_primes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

/-- `n` is a sum of three (not necessarily distinct) primes. -/

theorem goldbach_le_400 :
    ∀ m ∈ Finset.Icc 4 400, Even m → ∃ p ∈ Finset.Icc 2 100, Nat.Prime p ∧ Nat.Prime (m - p) := by
  decide

/-- **Base case.** Every odd `n` with `9 ≤ n ≤ 403` is a sum of three primes. -/
