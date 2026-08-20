import Mathlib
open Matrix
namespace QuantumInfoII

/-- Pauli matrices and the unnormalized Hadamard `M = √2·H`, over ℤ. -/

def X : Matrix (Fin 2) (Fin 2) ℤ := !![0,1;1,0]

def Z : Matrix (Fin 2) (Fin 2) ℤ := !![1,0;0,-1]

def M : Matrix (Fin 2) (Fin 2) ℤ := !![1,1;1,-1]

/-- Gottesman–Knill core: Hadamard conjugation swaps X and Z (unnormalized ⇒ factor 2). -/

theorem clifford_HXH : M * X * M = (2 : ℤ) • Z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X, Z, M, Matrix.mul_apply, Fin.sum_univ_succ]

/-- And swaps Z to X. -/
