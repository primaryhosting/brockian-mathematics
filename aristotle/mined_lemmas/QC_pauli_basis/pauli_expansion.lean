import Mathlib

/-!
# Pauli Basis
Category: Quantum Computing
Target: QC.pauli_basis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix

/-- The identity Pauli matrix `I`. -/

theorem pauli_expansion (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M = ((M 0 0 + M 1 1) / 2) • pauli 0 + ((M 0 1 + M 1 0) / 2) • pauli 1
      + (Complex.I * (M 0 1 - M 1 0) / 2) • pauli 2 + ((M 0 0 - M 1 1) / 2) • pauli 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli, pauliI, pauliX, pauliY, pauliZ, Complex.ext_iff] <;> ring_nf <;> simp

/-- The Pauli matrices are linearly independent over `ℂ`. -/
