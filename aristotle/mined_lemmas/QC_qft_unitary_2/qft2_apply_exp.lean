import Mathlib
/-!
# Qft Unitary 2
Category: Quantum Computing
Target: QC.qft_unitary_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The 2-qubit quantum Fourier transform matrix: the `4 × 4` matrix with entries
`(1/2) * ω ^ (j * k)`, where `ω = exp (2 * π * I / 4) = I` is a primitive 4-th root of unity. -/

theorem qft2_apply_exp (j k : Fin 4) :
    qft2 j k = (1 / 2 : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (j.val * k.val) / 4) := by
  have h : Complex.exp (2 * Real.pi * Complex.I / 4) = Complex.I := by
    rw [show (2 * (Real.pi : ℂ) * Complex.I / 4) = (Real.pi / 2 : ℝ) * Complex.I by push_cast; ring]
    rw [Complex.exp_mul_I]
    simp
  rw [qft2]
  congr 1
  conv_lhs => rw [← h]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The 2-qubit QFT matrix is unitary. -/
