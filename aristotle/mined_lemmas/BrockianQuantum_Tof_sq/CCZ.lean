import Mathlib
/-!
# Batch 14 — three-qubit gates Toffoli, Fredkin, CCZ (8x8 permutation/diagonal). All TRUE.
-/
namespace BrockianQuantum
open Matrix
/-- Toffoli (CCNOT): identity except swap of |110> and |111> (indices 6,7). -/

def CCZ : Matrix (Fin 8) (Fin 8) ℂ :=
  fun i j => if i = j then (if i = 7 then -1 else 1) else 0

