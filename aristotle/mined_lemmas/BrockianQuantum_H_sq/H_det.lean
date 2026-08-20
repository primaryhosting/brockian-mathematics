import Mathlib
/-!
# Batch 2 — Hadamard gate & basis change. All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix

theorem H_det : H.det = -1 := by
  rw [H, Matrix.det_fin_two_of]
  linear_combination -2 * hc_mul_hc

