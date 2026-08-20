import Mathlib
/-!
# Batch 16 — measurement projectors (qutrit completeness + Z-eigenprojector decomposition). All TRUE.
-/
namespace BrockianQuantum
open Matrix

def E1 : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![0,1,0]
