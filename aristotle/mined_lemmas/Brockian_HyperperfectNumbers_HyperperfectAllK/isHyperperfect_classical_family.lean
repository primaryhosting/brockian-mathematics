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

theorem isHyperperfect_classical_family {k p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpk : 2 * p = 3 * k + 1) (hqk : q = 3 * k + 4) : IsHyperperfect k (p ^ 2 * q) := by
  have hpq : p ≠ q := by omega
  refine isHyperperfect_primePow_mul_prime hp hq hpq (by norm_num) ?_
  have hpk' : (2 : ℤ) * p = 3 * k + 1 := by exact_mod_cast hpk
  have hqk' : (q : ℤ) = 3 * k + 4 := by exact_mod_cast hqk
  have key : ((p ^ 2 * q : ℕ) : ℤ)
      = ((k * (∑ i ∈ Finset.range 2, p ^ i) * (q + p) + 1 : ℕ) : ℤ) := by
    push_cast [Finset.sum_range_succ]
    linear_combination (((k : ℤ) + 2) * p + ((k : ℤ) + 1)) * hpk'
      + ((p : ℤ) ^ 2 - (k : ℤ) * (1 + p)) * hqk'
  exact_mod_cast key

/-- `6` is `1`-hyperperfect, i.e. perfect. -/
