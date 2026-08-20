import Mathlib
/-!
# Batch 4 — two-qubit gates CNOT, CZ, SWAP (4×4 over ℂ, basis |00>,|01>,|10>,|11>). All TRUE.
-/
namespace BrockianQuantum
open Matrix
/-- CNOT (control q0, target q1): swaps |10> ↔ |11>. -/

def SWAP : Matrix (Fin 4) (Fin 4) ℂ := !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1]

