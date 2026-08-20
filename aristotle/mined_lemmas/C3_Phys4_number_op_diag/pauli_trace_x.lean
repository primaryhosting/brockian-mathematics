import Mathlib
open Matrix
namespace C3.Phys4
-- `noncomputable` added: `Real.sqrt` has no executable code.

theorem pauli_trace_x : Matrix.trace Sx = 0 := by
  simp [Sx, Matrix.trace_fin_two]
end C3.Phys4

