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
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect when `n = 1 + k * (σ n - n - 1)`, i.e. `n` is one more than
`k` times the sum of its proper divisors other than `1`.  For `k = 1` this is exactly the
condition of being a perfect number. -/

theorem hyperperfect_eighteen_1333 : Hyperperfect 18 1333 := by
  have h : Hyperperfect 18 (31 * 43) :=
    (hyperperfect_mul_prime_iff (by norm_num) (by norm_num) (by norm_num)).mpr (by norm_num)
  norm_num at h
  exact h

/-- `51301 = 29 ^ 2 * 61` is `19`-hyperperfect. -/
