import Mathlib
/-!
# Batch 3 — phase gates S, T (Clifford+T). All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix

def PZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
/-- Phase gate S = diag(1, i). -/ noncomputable def S : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, Complex.I]
/-- T gate = diag(1, e^{iπ/4}). -/ noncomputable def T : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.exp (Complex.I * Real.pi / 4)]

