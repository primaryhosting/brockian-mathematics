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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `a ↦ ω ^ a.val` on `ZMod 5`. -/

lemma sum_omega_pow : 1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4 = 0 := by
  have h : (ω - 1) * (1 + ω + ω ^ 2 + ω ^ 3 + ω ^ 4) = ω ^ 5 - 1 := by ring
  rw [omega_pow_five, sub_self] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) omega_ne_one
  · exact h1

/-- Orthogonality for the character `e`: `∑ a, e (b * a) = 5` if `b = 0`, and `0` otherwise. -/
