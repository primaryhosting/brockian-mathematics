import Mathlib
/-!
# Batch 16 — measurement projectors (qutrit completeness + Z-eigenprojector decomposition). All TRUE.
-/
namespace BrockianQuantum
open Matrix

def E0 : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![1,0,0]
