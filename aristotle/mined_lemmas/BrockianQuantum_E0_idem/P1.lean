import Mathlib
/-!
# Batch 16 — measurement projectors (qutrit completeness + Z-eigenprojector decomposition). All TRUE.
-/
namespace BrockianQuantum
open Matrix

def P1 : Matrix (Fin 2) (Fin 2) ℂ := !![0,0; 0,1]
