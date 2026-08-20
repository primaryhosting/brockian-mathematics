import Mathlib
/-!
# Batch 10 — density matrices, projectors, Pauli traces. All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix

theorem PX_PZ_traceless : Matrix.trace (PX * PZ) = 0 := by
  simp [PX, PZ, Matrix.trace, Fin.sum_univ_two]
end BrockianQuantum

