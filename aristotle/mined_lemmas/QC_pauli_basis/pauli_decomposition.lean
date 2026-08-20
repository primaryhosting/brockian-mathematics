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

theorem pauli_decomposition (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M = ((M 0 0 + M 1 1) / 2) • pauliI + ((M 0 1 + M 1 0) / 2) • pauliX
      + (Complex.I * (M 0 1 - M 1 0) / 2) • pauliY + ((M 0 0 - M 1 1) / 2) • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliI, pauliX, pauliY, pauliZ] <;>
    ring_nf <;>
    simp [Complex.I_sq] <;>
    ring

/-- Uniqueness of the coefficients in a Pauli expansion. -/
