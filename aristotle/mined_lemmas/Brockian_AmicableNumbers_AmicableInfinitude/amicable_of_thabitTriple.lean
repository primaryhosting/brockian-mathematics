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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset ArithmeticFunction

namespace Brockian.AmicableNumbers

/-- The sum of the proper divisors of `n` (the divisors of `n` other than `n` itself). -/

theorem amicable_of_thabitTriple {n : ℕ} (hn : 1 ≤ n) (h : ThabitTriple n) :
    Amicable (2 ^ (n + 1) * ((3 * 2 ^ n - 1) * (3 * 2 ^ (n + 1) - 1)))
      (2 ^ (n + 1) * (9 * 2 ^ (2 * n + 1) - 1)) := by
  obtain ⟨hp, hq, hr⟩ := h
  have h1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
  have hpe : (3 * 2 ^ n - 1) + 1 = 3 * 2 ^ n := by omega
  have hqe : (3 * 2 ^ (n + 1) - 1) + 1 = 6 * 2 ^ n := by
    have h2 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
    omega
  have hre : (9 * 2 ^ (2 * n + 1) - 1) + 1 = 18 * 2 ^ n * 2 ^ n := by
    have h2 : 9 * (2 : ℕ) ^ (2 * n + 1) = 18 * 2 ^ n * 2 ^ n := by
      rw [two_mul, pow_succ, pow_add]; ring
    have h3 : (1 : ℕ) ≤ 2 ^ (2 * n + 1) := Nat.one_le_two_pow
    rw [← h2]
    omega
  exact amicable_of_thabit_data hn hp hq hr hpe hqe hre

/-- Sanity check of the rule: at `n = 1` it produces the classical amicable pair `(220, 284)`. -/
