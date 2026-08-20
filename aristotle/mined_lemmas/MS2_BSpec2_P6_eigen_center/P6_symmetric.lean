import Mathlib
open Matrix Polynomial
namespace MS2.BSpec2

theorem P6_symmetric : P6.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P6]

