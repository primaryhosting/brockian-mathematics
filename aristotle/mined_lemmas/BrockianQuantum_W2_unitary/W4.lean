import Mathlib
/-!
# Batch 8 — discrete/quantum Fourier transform (concrete 2- and 4-point). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix
/-- 2-point DFT (unnormalized) = √2 · Hadamard. -/

noncomputable def W4 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,1,1; 1,Complex.I,-1,-Complex.I; 1,-1,1,-1; 1,-Complex.I,-1,Complex.I]
/-- DFT² parity-reversal support. -/
