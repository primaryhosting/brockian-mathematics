import Mathlib
/-!
# Batch 2 — Hadamard gate & basis change. All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix

def PX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
