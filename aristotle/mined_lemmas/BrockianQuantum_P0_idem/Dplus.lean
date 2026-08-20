import Mathlib
/-!
# Batch 10 — density matrices, projectors, Pauli traces. All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix

noncomputable def Dplus : Matrix (Fin 2) (Fin 2) ℂ := !![1/2,1/2; 1/2,1/2]
