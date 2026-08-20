/-
# Hadamard XZ
Category: Quantum Computing
Target: QC.hadamard_XZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Matrix

/-- The Pauli `X` gate. -/

theorem hadamard_conj_X : H * PauliX * H = PauliZ := by
  unfold H PauliX PauliZ
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  have hinv : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
    rw [← mul_inv, sqrt_two_sq]
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring_nf

/-- **Hadamard XZ**: `H = (X + Z)/√2` and `H * X * H = Z`. -/
