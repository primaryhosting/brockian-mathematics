import Mathlib
/-!
# Batch 2 — Hadamard gate & basis change. All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix

theorem H_unitary : H * Hᴴ = 1 := by
  have hH : Hᴴ = H := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [H, Matrix.conjTranspose_apply, hc_conj]
  rw [hH, H_sq]

