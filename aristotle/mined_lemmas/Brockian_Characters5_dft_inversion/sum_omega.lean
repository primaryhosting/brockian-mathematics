import Mathlib

/-!
# Dft Inversion
Category: Characters
Target: Brockian.Characters5.dft_inversion
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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/

lemma sum_omega : 1 + omg + omg ^ 2 + omg ^ 3 + omg ^ 4 = 0 := by
  have key : (omg - 1) * (1 + omg + omg ^ 2 + omg ^ 3 + omg ^ 4) = omg ^ 5 - 1 := by ring
  rw [omega_pow_five, sub_self] at key
  rcases mul_eq_zero.mp key with h | h
  · exact absurd (sub_eq_zero.mp h) omega_ne_one
  · exact h

