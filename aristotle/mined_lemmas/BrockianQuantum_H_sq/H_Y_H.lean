import Mathlib
/-!
# Batch 2 — Hadamard gate & basis change. All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix

theorem H_Y_H : H * PY * H = -PY := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H, PY] <;> ring_nf <;> simp [hc_sq] <;> ring_nf

