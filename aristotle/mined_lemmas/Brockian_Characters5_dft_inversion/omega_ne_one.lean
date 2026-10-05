/-
# Dft Inversion
Category: Characters
Target: Brockian.Characters5.dft_inversion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/

lemma omega_ne_one : ω ≠ 1 := by
  rw [omega]
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) * (1 - n * 5) = 0 := by
    ring_nf; ring_nf at hn; linear_combination 5 * hn
  rcases mul_eq_zero.1 h2 with h | h
  · simp [hpi, hI] at h
  · have h1 : (1 : ℂ) = n * 5 := sub_eq_zero.mp h
    have h1' : (1 : ℤ) = n * 5 := by exact_mod_cast h1
    omega

