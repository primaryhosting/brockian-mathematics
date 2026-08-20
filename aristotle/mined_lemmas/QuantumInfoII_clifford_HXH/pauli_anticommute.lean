import Mathlib
open Matrix
namespace QuantumInfoII

/-- Pauli matrices and the unnormalized Hadamard `M = √2·H`, over ℤ. -/

theorem pauli_anticommute : X * Z = - (Z * X) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X, Z, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The classical (local hidden-variable) Bell/CHSH bound: every ±1 assignment gives
    `|CHSH| ≤ 2`, versus the quantum Tsirelson value `2√2`. -/
