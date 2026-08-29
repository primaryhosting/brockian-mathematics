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

lemma root_pow_eq_one {N : ℕ} (hN : 0 < N) (d : ℤ) :
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / (N : ℂ))) ^ N = 1 := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [← Complex.exp_nat_mul]
  have h2 : (N : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / (N : ℂ))
      = (d : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by field_simp
  rw [h2, Complex.exp_int_mul_two_pi_mul_I]

/-- The geometric sum of a nontrivial `N`-th root of unity vanishes. -/
