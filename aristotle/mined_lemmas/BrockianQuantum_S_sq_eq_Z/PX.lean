import Mathlib
/-!
# Batch 3 — phase gates S, T (Clifford+T). All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix

def PX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
