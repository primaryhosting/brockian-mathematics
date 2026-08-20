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

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect when `k ≥ 1`, `n > 1` and `n = 1 + k * (σ n - n - 1)`, i.e. `k`
times the sum of the divisors of `n` other than `1` and `n` equals `n - 1`.
The equation is written without truncated subtraction as `n + k * (n + 1) = 1 + k * σ n`. -/

theorem isHyperperfect_mul_of_prime {p : ℕ} (hp : p.Prime) (hq : (p ^ 2 - p + 1).Prime) :
    IsHyperperfect (p - 1) (p * (p ^ 2 - p + 1)) := by
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have hsq : (a + 2) ^ 2 = a ^ 2 + 4 * a + 4 := by ring
  have hq' : (a + 2) ^ 2 - (a + 2) + 1 = a ^ 2 + 3 * a + 3 := by omega
  rw [hq'] at hq ⊢
  have hlt : a + 2 < a ^ 2 + 3 * a + 3 := by nlinarith [sq_nonneg a]
  have hne : a + 2 ≠ a ^ 2 + 3 * a + 3 := by omega
  refine ⟨by omega, ?_, ?_⟩
  · nlinarith [sq_nonneg a]
  · rw [sigma_one_mul_of_primes hp hq hne]
    have hk : a + 2 - 1 = a + 1 := by omega
    rw [hk]
    ring

/-- Each such `p * q` is at least `p`, so the family is unbounded. -/
