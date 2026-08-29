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
`i ^ (j * k) / 2`, where `i` is the primitive fourth root of unity. -/

theorem qft2_eq :
    qft2 = (2 : ℂ)⁻¹ •
      !![1, 1, 1, 1;
         1, Complex.I, -1, -Complex.I;
         1, -1, 1, -1;
         1, -Complex.I, -1, Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qft2, pow_succ, Complex.I_mul_I] <;> ring

/-- The 2-qubit QFT matrix is unitary. -/
