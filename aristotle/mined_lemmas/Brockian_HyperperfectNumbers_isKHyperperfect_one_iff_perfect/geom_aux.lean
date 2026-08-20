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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect if `n = 1 + k * (σ n - n - 1)`, i.e. `n` is one plus `k` times the
sum of its proper divisors other than `1`.  The definition is stated in the subtraction-free
form `k * σ n + 1 = (k + 1) * n + k`. -/

private theorem geom_aux (r t : ℕ) :
    r * (∑ k ∈ range t, (r + 1) ^ k) + 1 = (r + 1) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
      calc r * (∑ k ∈ range (t + 1), (r + 1) ^ k) + 1
          = (r * (∑ k ∈ range t, (r + 1) ^ k) + 1) + r * (r + 1) ^ t := by
            rw [Finset.sum_range_succ]; ring
        _ = (r + 1) ^ t + r * (r + 1) ^ t := by rw [ih]
        _ = (r + 1) ^ (t + 1) := by ring

/-- **Minoli's family of hyperperfect numbers.**  If `q` and `p` are primes with
`q ^ t + 1 = p + q` and `t ≥ 2`, then `q ^ (t - 1) * p` is `(q - 1)`-hyperperfect.
For `q = 2` this specializes to the Euclid family of (`1`-hyperperfect) perfect numbers
`2 ^ (t - 1) * (2 ^ t - 1)` associated with Mersenne primes. -/
