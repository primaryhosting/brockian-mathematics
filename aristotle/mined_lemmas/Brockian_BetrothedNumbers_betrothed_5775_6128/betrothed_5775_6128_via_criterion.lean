import Mathlib

/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Brockian.BetrothedNumbers

open Finset

set_option maxRecDepth 100000

/-- The sum-of-divisors function `σ₁ n = ∑_{d ∣ n} d`. -/

theorem betrothed_5775_6128_via_criterion :
    Nat.Prime 383 ∧ (6128 : ℕ) = 2 ^ 4 * 383 ∧ IsBetrothedPair 5775 (2 ^ 4 * 383) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  refine isBetrothedPair_of_sigma_criterion (k := 4) (p := 383) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ?_
  rw [sigma1_5775]
  norm_num

end Brockian.BetrothedNumbers

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

