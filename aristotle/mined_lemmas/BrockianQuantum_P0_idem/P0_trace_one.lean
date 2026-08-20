import Mathlib
/-!
# Batch 10 — density matrices, projectors, Pauli traces. All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix

theorem P0_trace_one : Matrix.trace P0 = 1 := by
  simp [P0, Matrix.trace, Fin.sum_univ_two]

