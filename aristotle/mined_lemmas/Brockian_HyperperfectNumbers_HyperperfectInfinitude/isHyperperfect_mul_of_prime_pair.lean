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

namespace Brockian.HyperperfectNumbers

open Finset

/-- `sigmaOne n` is the sum of all divisors of `n`, usually written `σ₁ (n)`. -/

lemma isHyperperfect_mul_of_prime_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hqe : q + p = p * p + 1) : IsHyperperfect (p - 1) (p * q) := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  have hk : 1 ≤ k := by have := hp.two_le; omega
  have hexp : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
  have hq' : q = k * k + k + 1 := by linarith
  subst hq'
  have hkk : 1 ≤ k * k := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hpq : k + 1 ≠ k * k + k + 1 := by omega
  refine ⟨by omega, ?_, ?_⟩
  · have : 2 ≤ k + 1 := by omega
    calc 1 < 2 * 1 := by omega
      _ ≤ (k + 1) * (k * k + k + 1) := Nat.mul_le_mul this (by omega)
  · rw [Nat.add_sub_cancel, sigmaOne_mul_of_primes hp hq hpq]
    ring

/-- `21 = 3 * 7` is `2`-hyperperfect. -/
