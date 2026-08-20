import Mathlib
open Matrix
namespace QuantumInfoII

/-- Pauli matrices and the unnormalized Hadamard `M = √2·H`, over ℤ. -/

theorem clifford_HXH : M * X * M = (2 : ℤ) • Z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X, Z, M, Matrix.mul_apply, Fin.sum_univ_succ]

/-- And swaps Z to X. -/
