import Mathlib
/-!
# Batch 4 — two-qubit gates CNOT, CZ, SWAP (4×4 over ℂ, basis |00>,|01>,|10>,|11>). All TRUE.
-/
namespace BrockianQuantum
open Matrix
/-- CNOT (control q0, target q1): swaps |10> ↔ |11>. -/

theorem CNOT_unitary : CNOT * CNOTᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CNOT, Matrix.mul_apply, Fin.sum_univ_four, Matrix.conjTranspose_apply]

