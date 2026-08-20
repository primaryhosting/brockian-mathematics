import Mathlib
/-!
# Batch 2 — Hadamard gate & basis change. All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix

theorem H_sq : H * H = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H, hc_mul_hc] <;> norm_num

