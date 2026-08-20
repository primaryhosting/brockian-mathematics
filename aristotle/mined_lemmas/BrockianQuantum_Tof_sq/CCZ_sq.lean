import Mathlib
/-!
# Batch 14 — three-qubit gates Toffoli, Fredkin, CCZ (8x8 permutation/diagonal). All TRUE.
-/
namespace BrockianQuantum
open Matrix
/-- Toffoli (CCNOT): identity except swap of |110> and |111> (indices 6,7). -/

theorem CCZ_sq : CCZ * CCZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, CCZ]

