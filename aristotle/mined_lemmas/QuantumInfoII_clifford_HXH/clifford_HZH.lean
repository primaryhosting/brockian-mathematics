import Mathlib
open Matrix
namespace QuantumInfoII

/-- Pauli matrices and the unnormalized Hadamard `M = √2·H`, over ℤ. -/

theorem clifford_HZH : M * Z * M = (2 : ℤ) • X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X, Z, M, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Pauli X and Z anticommute — the algebraic seed of the uncertainty principle. -/
