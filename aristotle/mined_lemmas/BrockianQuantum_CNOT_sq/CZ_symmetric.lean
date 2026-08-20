import Mathlib
/-!
# Batch 4 — two-qubit gates CNOT, CZ, SWAP (4×4 over ℂ, basis |00>,|01>,|10>,|11>). All TRUE.
-/
namespace BrockianQuantum
open Matrix
/-- CNOT (control q0, target q1): swaps |10> ↔ |11>. -/

theorem CZ_symmetric : CZᵀ = CZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CZ, Matrix.transpose_apply]

end BrockianQuantum

