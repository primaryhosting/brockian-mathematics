/-
# Ray Indicator Eq Char Sum
Category: Characters
Target: Brockian.Characters5.rayIndicator_eq_charSum
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

namespace Brockian
namespace Characters5

/-- The primitive fifth root of unity `ω = exp(2πi/5)`. -/

lemma sum_omega_pow : 1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4 = 0 := by
  have hfac : (ω - 1) * (1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4) = ω ^ 5 - 1 := by ring
  rw [omega_pow_five, sub_self] at hfac
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) omega_ne_one
  · exact h

