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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AmicableNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The sum of all (positive) divisors of `n`.  For `n = 0` this is `0`. -/

theorem isAmicablePair_of_thabitIndex {k : ℕ} (h : ThabitIndex k) :
    IsAmicablePair (2 ^ (k + 2) * (3 * 2 ^ (k + 1) - 1) * (3 * 2 ^ (k + 2) - 1))
      (2 ^ (k + 2) * (9 * 2 ^ (2 * k + 3) - 1)) := by
  obtain ⟨hp, hq, hr⟩ := h
  have h1 : 1 ≤ (2 : ℕ) ^ (k + 1) := Nat.one_le_two_pow
  have h2 : 1 ≤ (2 : ℕ) ^ (k + 2) := Nat.one_le_two_pow
  have h3 : 1 ≤ (2 : ℕ) ^ (2 * k + 3) := Nat.one_le_two_pow
  exact isAmicablePair_thabit hp hq hr (by omega) (by omega) (by omega)

/-- `k = 0` is a Thâbit index; the pair it produces is `(220, 284)`. -/
