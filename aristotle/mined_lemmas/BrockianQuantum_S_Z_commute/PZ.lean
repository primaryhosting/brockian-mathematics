import Mathlib
/-!
# Batch 13 — Clifford conjugations (H, S normalize the Pauli group). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix

def PZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

