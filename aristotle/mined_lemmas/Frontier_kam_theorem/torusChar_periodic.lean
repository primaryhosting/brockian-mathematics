/-
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

/-- The character `x ↦ e^{2πi k x}` on the circle `ℝ / ℤ`. -/

lemma torusChar_periodic (k : ℤ) (x : ℝ) : torusChar k (x + 1) = torusChar k x := by
  rw [torusChar_add]
  have : torusChar k 1 = 1 := by
    unfold torusChar
    rw [Complex.exp_eq_one_iff]
    exact ⟨k, by push_cast; ring⟩
  rw [this, mul_one]

/-- Small divisors do not vanish: for an irrational frequency `ω` and a nonzero
frequency `k`, `e^{2πi k ω} ≠ 1`. -/
