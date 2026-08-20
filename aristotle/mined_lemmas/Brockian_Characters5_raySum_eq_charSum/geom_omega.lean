/-
# Ray Sum Eq Char Sum
Category: Characters
Target: Brockian.Characters5.raySum_eq_charSum
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
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e` of `ZMod 5` with values in `ℂ`, `e x = ω ^ x.val`. -/

lemma geom_omega : 1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4 = 0 := by
  have h : (ω - 1) * (1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4) = ω ^ 5 - 1 := by ring
  rw [omega_pow_five] at h
  have hne : ω - 1 ≠ 0 := sub_ne_zero.mpr omega_ne_one
  have h0 : (ω - 1) * (1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4) = 0 := by rw [h]; ring
  exact (mul_eq_zero.mp h0).resolve_left hne

