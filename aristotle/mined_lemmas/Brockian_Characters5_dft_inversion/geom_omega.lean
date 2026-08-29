/-
# Dft Inversion
Category: Characters
Target: Brockian.Characters5.dft_inversion
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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/

lemma geom_omega : 1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
  have h : (omega - 1) * (1 + omega + omega ^ 2 + omega ^ 3 + omega ^ 4) = 0 := by
    have := omega_pow_five
    linear_combination this
  rcases mul_eq_zero.mp h with h1 | h2
  · exact absurd (sub_eq_zero.mp h1) omega_ne_one
  · exact h2

