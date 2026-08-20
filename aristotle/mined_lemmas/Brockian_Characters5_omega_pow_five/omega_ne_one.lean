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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/

theorem omega_ne_one : omega ≠ 1 := by
  intro h
  rw [omega, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h5 : (1 : ℂ) = 5 * (n : ℂ) := by
    field_simp at hn
    exact hn
  have : (1 : ℤ) = 5 * n := by exact_mod_cast h5
  omega

/-- The sum of all fifth roots of unity vanishes. -/
