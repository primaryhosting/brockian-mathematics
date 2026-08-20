import Mathlib
/-!
# Batch 10 — density matrices, projectors, Pauli traces. All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix

theorem PX_traceless : Matrix.trace PX = 0 := by
  simp [PX, Matrix.trace, Fin.sum_univ_two]

