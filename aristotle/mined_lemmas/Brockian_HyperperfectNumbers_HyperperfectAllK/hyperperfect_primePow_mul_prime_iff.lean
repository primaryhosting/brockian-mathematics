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

theorem hyperperfect_primePow_mul_prime_iff {k p t q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Hyperperfect k (p ^ t * q) ↔
      (q : ℤ) * ((k + 1) * (p : ℤ) ^ t - k * (sigmaPrimePow p t : ℤ))
        = k * (sigmaPrimePow p t : ℤ) - k + 1 := by
  have hone : 1 < p ^ t * q := by
    have hq2 : 2 ≤ q := hq.two_le
    have hpt : 1 ≤ p ^ t := Nat.one_le_pow _ _ hp.pos
    calc 1 < 2 := by norm_num
      _ ≤ 1 * q := by simpa using hq2
      _ ≤ p ^ t * q := by
          exact Nat.mul_le_mul_right q hpt
  rw [Hyperperfect, sigma_one_primePow_mul_prime hp hq hpq]
  simp only [hone, true_and]
  push_cast
  constructor <;> intro h <;> linear_combination h

/-- Sufficient condition: solutions of the Diophantine equation give `k`-hyperperfect numbers. -/
