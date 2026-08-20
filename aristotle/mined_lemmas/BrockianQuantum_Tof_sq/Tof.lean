import Mathlib
/-!
# Batch 14 — three-qubit gates Toffoli, Fredkin, CCZ (8x8 permutation/diagonal). All TRUE.
-/
namespace BrockianQuantum
open Matrix
/-- Toffoli (CCNOT): identity except swap of |110> and |111> (indices 6,7). -/

def Tof : Matrix (Fin 8) (Fin 8) ℂ :=
  fun i j => if i = 6 then (if j = 7 then 1 else 0)
             else if i = 7 then (if j = 6 then 1 else 0)
             else if i = j then 1 else 0
/-- Fredkin (CSWAP): identity except swap of |101> and |110> (indices 5,6). -/
