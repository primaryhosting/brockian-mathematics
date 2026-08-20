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
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.HyperperfectNumbers

open scoped BigOperators

/-- `n` is `k`-hyperperfect if `n > 1` and `n = 1 + k * (σ(n) - n - 1)`, i.e. `n` is one plus
`k` times the sum of the divisors of `n` other than `1` and `n`. -/

lemma isHyperperfect_prime_mul_prime_iff {k p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) : IsHyperperfect k (p * q) ↔ p * q = 1 + k * (p + q) := by
  have hσ : ArithmeticFunction.sigma 1 (p * q) - p * q - 1 = p + q := by
    rw [sigma_one_prime_mul_prime hp hq hne]; ring_nf; omega
  constructor
  · rintro ⟨-, h⟩; rw [hσ] at h; exact h
  · intro h
    refine ⟨?_, by rw [hσ]; exact h⟩
    have := hp.two_le
    have := hq.two_le
    nlinarith

/-- Sufficient condition: if `d * e = k ^ 2 + 1` and both `k + d` and `k + e` are prime, then
`(k + d) * (k + e)` is `k`-hyperperfect. -/
