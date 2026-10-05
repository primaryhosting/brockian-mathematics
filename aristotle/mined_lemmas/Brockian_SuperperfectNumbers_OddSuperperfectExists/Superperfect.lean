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

def Superperfect (n : ℕ) : Prop := σ 1 (σ 1 n) = 2 * n

instance decidableSuperperfect (n : ℕ) : Decidable (Superperfect n) :=
  inferInstanceAs (Decidable (σ 1 (σ 1 n) = 2 * n))

/-! ### Basic divisor-sum estimates -/

/-- If `a` is a divisor of `N` with `1 < a < N`, then `1`, `a` and `N` are three distinct
divisors of `N`, so `σ N ≥ N + a + 1`. -/
