-- # Sum E Mul
-- Category: Characters
-- Target: Brockian.Characters5.sum_e_mul
-- Verification: pending
-- Provenance: Aristotle theorem prover (Harmonic)

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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/

lemma omega_ne_one : omega ≠ 1 := by
  intro hone
  rw [omega, Complex.exp_eq_one_iff] at hone
  obtain ⟨n, hn⟩ := hone
  have hA : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h : ((5 : ℂ) * n - 1) * (2 * Real.pi * Complex.I) = 0 := by
    linear_combination (-5 : ℂ) * hn
  have h2 : (5 : ℂ) * n - 1 = 0 := by
    rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd h' hA
  have h3 : (5 : ℤ) * n = 1 := by exact_mod_cast sub_eq_zero.mp h2
  omega

/-- The five fifth roots of unity sum to zero. -/
