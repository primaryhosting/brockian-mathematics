import Mathlib
/-!
# Batch 8 — discrete/quantum Fourier transform (concrete 2- and 4-point). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix
/-- 2-point DFT (unnormalized) = √2 · Hadamard. -/

def P4 : Matrix (Fin 4) (Fin 4) ℂ := !![1,0,0,0; 0,0,0,1; 0,0,1,0; 0,1,0,0]

