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

/-- The primitive fifth root of unity. -/

lemma omega_ne_one : omega ≠ 1 := by
  intro h
  rw [omega, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have h5 : (5 : ℂ) * n = 1 := by
    field_simp at hn
    linear_combination -hn
  have : ((5 * n : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by push_cast; linear_combination h5
  have h5' : (5 : ℤ) * n = 1 := by exact_mod_cast this
  omega

