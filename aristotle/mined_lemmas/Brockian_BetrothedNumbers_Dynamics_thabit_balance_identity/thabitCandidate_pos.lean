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
# Thabit Balance Identity
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.thabit_balance_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers.Dynamics

/-- The Thabit-style candidate attached to the parameters `k` and `p`:
`m = (2 ^ k - 1) * (p + 2)`.  (The subtraction is harmless: `1 ≤ 2 ^ k`.) -/

theorem thabitCandidate_pos {k p : ℕ} (h : SigmaCriterion k p) :
    0 < thabitCandidate k p := by
  rcases Nat.eq_zero_or_pos (thabitCandidate k p) with hm | hm
  · rw [SigmaCriterion, hm] at h
    have h0 : σ 1 0 = 0 := by simp
    rw [h0, zero_add] at h
    have h2 : 2 ≤ 2 ^ (k + 1) := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith
  · exact hm

/-- The balance identity, transported to the sum of proper divisors. -/
