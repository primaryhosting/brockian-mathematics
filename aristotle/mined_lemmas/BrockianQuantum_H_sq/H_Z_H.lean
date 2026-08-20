import Mathlib
/-!
# Batch 2 — Hadamard gate & basis change. All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix

theorem H_Z_H : H * PZ * H = PX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H, PX, PZ, hc_mul_hc] <;> ring_nf

