import Mathlib
open Matrix
namespace C3.Phys4
-- `noncomputable` added: `Real.sqrt` has no executable code.

theorem pauli_prod_xy : Sx * Sy = Complex.I • (!![1,0;0,-1] : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Sx, Sy, Matrix.mul_apply, Fin.sum_univ_succ]
