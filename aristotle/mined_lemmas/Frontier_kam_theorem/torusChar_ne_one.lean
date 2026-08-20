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

lemma torusChar_ne_one {ω : ℝ} (hω : Irrational ω) {k : ℤ} (hk : k ≠ 0) :
    torusChar k ω ≠ 1 := by
  intro hcon
  rw [torusChar, Complex.exp_eq_one_iff] at hcon
  obtain ⟨n, hn⟩ := hcon
  have hI : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  push_cast at hn
  have h2 : (k : ℂ) * (ω : ℂ) = (n : ℂ) := by
    apply mul_left_cancel₀ hI
    linear_combination hn
  have h3 : (k : ℝ) * ω = (n : ℝ) := by exact_mod_cast h2
  exact (Irrational.intCast_mul hω hk).ne_int n h3

/-- **Solution of the homological equation.** For an irrational frequency `ω` and a
zero-mean trigonometric polynomial `f = trigPoly s c` (zero mean is encoded by
`0 ∉ s`), the function `homSol ω s c` solves `u (x + ω) - u x = f x`. -/
