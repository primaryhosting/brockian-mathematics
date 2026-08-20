import Mathlib
/-!
# Batch 10 — density matrices, projectors, Pauli traces. All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix

def PX : Matrix (Fin 2) (Fin 2) ℂ := !![0,1; 1,0]
