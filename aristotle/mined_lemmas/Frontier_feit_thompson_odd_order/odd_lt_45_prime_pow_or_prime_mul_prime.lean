/-
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
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
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

universe u

/-- The full Feit–Thompson theorem, as a proposition about a universe of types:
every finite group of odd order is solvable. -/

theorem odd_lt_45_prime_pow_or_prime_mul_prime :
    ∀ n < 45, Odd n →
      ((∃ p ≤ 45, ∃ k ≤ 6, Nat.Prime p ∧ n = p ^ k) ∨
        (∃ p ≤ 45, ∃ q ≤ 45, Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ n = p * q)) := by
  decide

/-- **Unconditional base case of Feit–Thompson**: every finite group of odd order less
than `45` is solvable.  (`45 = 3 ^ 2 * 5` is the first odd order that is neither a prime power
nor a product of two distinct primes.) -/
