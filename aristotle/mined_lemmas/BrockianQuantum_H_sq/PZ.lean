import Mathlib
/-!
# Batch 2 — Hadamard gate & basis change. All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix

def PZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- `hc * hc = 1/2`, since `(√2)^2 = 2`. -/
