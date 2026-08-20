import Mathlib
open Matrix
namespace QuantumInfoII

/-- Pauli matrices and the unnormalized Hadamard `M = √2·H`, over ℤ. -/

def Z : Matrix (Fin 2) (Fin 2) ℤ := !![1,0;0,-1]
