import Mathlib
open Matrix
namespace C3.Phys4
-- `noncomputable` added: `Real.sqrt` has no executable code.

noncomputable def a : Matrix (Fin 3) (Fin 3) ℝ := !![0,1,0;0,0,Real.sqrt 2;0,0,0]

noncomputable def ad : Matrix (Fin 3) (Fin 3) ℝ := !![0,0,0;1,0,0;0,Real.sqrt 2,0]

theorem number_op_diag : (ad * a).IsDiag := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [ad, a, Matrix.mul_apply, Fin.sum_univ_succ]
