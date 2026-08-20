import Mathlib
/-!
# Batch 15 — single-qubit Z-rotations Rz(θ) = diag(e^{-iθ/2}, e^{iθ/2}) in SU(2). All TRUE.
-/
namespace BrockianQuantum
open Matrix

theorem Rz_zero : Rz 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rz]

