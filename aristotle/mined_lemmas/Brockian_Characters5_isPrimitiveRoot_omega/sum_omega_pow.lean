/-
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/

theorem sum_omega_pow : ∑ k ∈ Finset.range 5, omega ^ k = 0 := by
  have h : (omega - 1) * ∑ k ∈ Finset.range 5, omega ^ k = 0 := by
    have := geom_sum_mul omega 5
    rw [mul_comm] at this
    rw [this, omega_pow_five, sub_self]
  rcases mul_eq_zero.mp h with h1 | h2
  · exact absurd (sub_eq_zero.mp h1) omega_ne_one
  · exact h2

