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
/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

open scoped BigOperators

namespace Brockian
namespace ZumkellerNumbers

/-- A positive natural number `n` is *Zumkeller* if its set of divisors can be split into
two blocks having the same sum. -/

theorem sigma_prime_pow_mul_pred_le (p a : ℕ) (hp : p.Prime) :
    (∑ d ∈ (p ^ a).divisors, d) * (p - 1) ≤ p ^ a * p := by
  rw [Nat.sum_divisors_prime_pow hp]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  simp only [Nat.add_sub_cancel]
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, add_mul]
    calc (∑ x ∈ Finset.range (a + 1), (q + 1) ^ x) * q + (q + 1) ^ (a + 1) * q
        ≤ (q + 1) ^ a * (q + 1) + (q + 1) ^ (a + 1) * q := by gcongr
      _ = (q + 1) ^ (a + 1) * (q + 1) := by ring

/-- The sum-of-divisors function factors over the prime factorisation. -/
