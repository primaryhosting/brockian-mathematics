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

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.AmicableNumbers

/-- The sum of the proper divisors of `n` (the "aliquot sum"). -/

theorem thabit_mem_amicableNumbers {n : ℕ} (hn : IsThabitIndex n) :
    2 ^ (n + 1) * ((3 * 2 ^ n - 1) * (3 * 2 ^ (n + 1) - 1)) ∈ AmicableNumbers := by
  obtain ⟨h1, hp, hq, hr⟩ := hn
  have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  refine ⟨2 ^ (n + 1) * (9 * 2 ^ (2 * n + 1) - 1), ?_⟩
  have hrw : 2 ^ (n + 1) * ((3 * 2 ^ n - 1) * (3 * 2 ^ (n + 1) - 1))
      = 2 * 2 ^ n * (3 * 2 ^ n - 1) * (3 * 2 ^ (n + 1) - 1) := by ring
  have hrw2 : 2 ^ (n + 1) * (9 * 2 ^ (2 * n + 1) - 1)
      = 2 * 2 ^ n * (9 * 2 ^ (2 * n + 1) - 1) := by ring
  rw [hrw, hrw2]
  have hpow1 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
  have h9 : 9 * 2 ^ (2 * n + 1) = 18 * (2 ^ n) ^ 2 := by
    rw [← pow_mul]
    ring
  exact thabit_amicable h1 rfl hp (by omega) hq (by omega) hr (by omega)

/-- **Conditional infinitude of amicable numbers.**
If there are infinitely many Thabit indices — that is, if for every `N` there is some `n ≥ N`
with `3·2ⁿ - 1`, `3·2ⁿ⁺¹ - 1` and `9·2²ⁿ⁺¹ - 1` all prime — then there are infinitely many
amicable numbers. -/
