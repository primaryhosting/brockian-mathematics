import Mathlib
open Matrix
namespace QuantumInfoII

/-- Pauli matrices and the unnormalized Hadamard `M = √2·H`, over ℤ. -/

def M : Matrix (Fin 2) (Fin 2) ℤ := !![1,1;1,-1]

/-- Gottesman–Knill core: Hadamard conjugation swaps X and Z (unnormalized ⇒ factor 2). -/
