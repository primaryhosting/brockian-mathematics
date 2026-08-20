import Mathlib
/-!
# Batch 2 — Hadamard gate & basis change. All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix

theorem H_eq_sum : H = hc • (PX + PZ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H, PX, PZ]
end BrockianQuantum

