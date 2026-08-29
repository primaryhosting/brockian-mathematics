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

open scoped BigOperators
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.HyperperfectNumbers

/-! ## The notion of a `k`-hyperperfect number -/

/-- `IsHyperperfect k n` says that `n` is a `k`-hyperperfect number, i.e. `n > 1` and
`n = 1 + k * (σ n - n - 1)`, where `σ n` is the sum of the divisors of `n`.

The equation is written in the subtraction-free form `n + k * (n + 1) = k * σ n + 1`,
which is equivalent over `ℤ` to `n = 1 + k * (σ n - n - 1)`; this avoids the pitfalls of
truncated natural subtraction (which would make `n = 1` a spurious solution). -/

theorem geom_sum_step (p m : ℕ) :
    p * (∑ i ∈ Finset.range m, p ^ i) + 1 = (∑ i ∈ Finset.range m, p ^ i) + p ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hpow : p ^ (m + 1) = p * p ^ m := by ring
      rw [Finset.sum_range_succ, mul_add, hpow]
      omega

/-- The sum of divisors of a prime. -/
