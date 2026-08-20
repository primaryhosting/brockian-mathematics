import Mathlib
open Matrix
namespace C3.Phys4
-- `noncomputable` added: `Real.sqrt` has no executable code.

theorem number_op_diag : (ad * a).IsDiag := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [ad, a, Matrix.mul_apply, Fin.sum_univ_succ]
