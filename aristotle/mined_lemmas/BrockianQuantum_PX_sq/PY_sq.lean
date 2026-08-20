import Mathlib
/-!
# Batch 1 — single-qubit Pauli algebra (stabilizer/gate foundations). All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix
/-- Pauli X. -/           def PX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
/-- Pauli Y. -/ noncomputable def PY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
/-- Pauli Z. -/           def PZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]


theorem PY_sq : PY * PY = 1 := by
  simp [PY, Matrix.one_fin_two, Complex.I_mul_I]
