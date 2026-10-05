-- /-!
-- # Qft Unitary 4
-- Category: Quantum Computing
-- Target: QC.qft_unitary_4
-- Verification: pending
-- Provenance: Aristotle theorem prover (Harmonic)
-- -/

import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
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

open scoped Matrix

namespace QC

/-- The `N`-point discrete (quantum) Fourier transform matrix:
`(qftMatrix N) j k = N^(-1/2) * exp (2πi·jk/N)`. -/

lemma root_ne_one {N : ℕ} (hN : 0 < N) {d : ℤ} (hd : ¬ ((N : ℤ) ∣ d)) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / (N : ℂ)) ≠ 1 := by
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp at hn
  have hd' : (d : ℤ) = (N : ℤ) * n := by exact_mod_cast hn
  exact hd ⟨n, hd'⟩

/-- `exp (2πi·d/N)` is an `N`-th root of unity. -/
