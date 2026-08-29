/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex Finset Matrix

/-- The primitive `n`-th root of unity `exp (2 π i / n)` used in the QFT. -/

lemma conj_qftOmega (n : ℕ) :
    (starRingEnd ℂ) (qftOmega n) = (qftOmega n)⁻¹ := by
  have h : (2 : ℂ) * Real.pi * Complex.I / n = ((2 * Real.pi / n : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hnorm : ‖qftOmega n‖ = 1 := by
    rw [qftOmega, h, Complex.norm_exp_ofReal_mul_I]
  exact (Complex.inv_eq_conj hnorm).symm

/-- Orthogonality of the columns of the (unnormalized) QFT matrix. -/
