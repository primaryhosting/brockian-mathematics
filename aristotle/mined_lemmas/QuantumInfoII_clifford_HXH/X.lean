import Mathlib
open Matrix
namespace QuantumInfoII

/-- Pauli matrices and the unnormalized Hadamard `M = √2·H`, over ℤ. -/

def X : Matrix (Fin 2) (Fin 2) ℤ := !![0,1;1,0]
