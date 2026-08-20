import Mathlib
open Matrix
namespace C2.QI4

theorem cz_diagonal : CZ.IsDiag := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [CZ]

end C2.QI4

