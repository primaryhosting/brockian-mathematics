import Mathlib
open Matrix
namespace C6.QC7

theorem pauli_trace_zero : Matrix.trace X = 0 ∧ Matrix.trace Y = 0 ∧ Matrix.trace Z = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [X, Y, Z, Matrix.trace_fin_two]

