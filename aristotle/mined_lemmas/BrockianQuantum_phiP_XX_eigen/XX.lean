import Mathlib
/-!
# Batch 5 — Bell states as stabilizer eigenvectors. All TRUE; bare `import Mathlib`.
Basis order |00>,|01>,|10>,|11> = 0,1,2,3.  XX = X⊗X, ZZ = Z⊗Z.
-/
namespace BrockianQuantum
open Matrix

def XX : Matrix (Fin 4) (Fin 4) ℂ := !![0,0,0,1; 0,0,1,0; 0,1,0,0; 1,0,0,0]
