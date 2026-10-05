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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.SuperperfectNumbers

/-- A natural number `n` is *superperfect* if `σ (σ n) = 2 * n`, where `σ` is the
sum-of-divisors function. -/

theorem superperfect_two_pow_of_prime {k : ℕ} (hp : Nat.Prime (2 ^ (k + 1) - 1)) :
    Superperfect (2 ^ k) := by
  have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  unfold Superperfect
  rw [sigma_two_pow, sigma_prime hp]
  have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  omega

example : Superperfect 16 := by decide

/-! ### Constraints on odd superperfect numbers -/

/-- `1` is not superperfect. -/
