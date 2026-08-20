import Mathlib
open Matrix
namespace C3.QI5

theorem cnot_det : CNOT.det = -1 := by
  simp [CNOT, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

end C3.QI5

