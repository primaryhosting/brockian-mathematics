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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- `IsKHyperperfect k n` states that `n` is a `k`-hyperperfect number, i.e. `k > 0`, `n > 1` and
`n = 1 + k * (σ n - n - 1)`, written here in the subtraction-free form
`k * σ n + 1 = (k + 1) * n + k`. -/

lemma sigma_one_prime {p : ℕ} (hp : p.Prime) : ArithmeticFunction.sigma 1 p = p + 1 := by
  simp [ArithmeticFunction.sigma_one_apply, hp.divisors, Finset.sum_pair hp.one_lt.ne,
    Nat.add_comm]

/-- The divisor-sum of a prime power is the corresponding geometric sum. -/
