import Mathlib

/-!
# Parseval
Category: Characters
Target: Brockian.Characters5.parseval
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
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character of `ZMod 5` associated with `ω`. -/

theorem e_conj (k : ZMod 5) : (starRingEnd ℂ) (e k) = e (-k) := by
  have h1 : e k * e (-k) = 1 := by rw [← e_add]; simp [e_zero]
  have hne : e k ≠ 0 := by
    intro h
    have := norm_e k
    rw [h] at this
    simp at this
  have h2 : e k * (starRingEnd ℂ) (e k) = 1 := by
    rw [Complex.mul_conj']
    have := norm_e k
    rw [this]
    norm_num
  exact mul_left_cancel₀ hne (h2.trans h1.symm)

/-- Orthogonality of the characters. -/
