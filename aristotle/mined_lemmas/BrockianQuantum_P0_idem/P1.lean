import Mathlib
/-!
# Batch 10 — density matrices, projectors, Pauli traces. All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix

def P1 : Matrix (Fin 2) (Fin 2) ℂ := !![0,0; 0,1]
