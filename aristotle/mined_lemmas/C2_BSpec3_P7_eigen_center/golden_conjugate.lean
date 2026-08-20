import Mathlib
open Matrix Polynomial
namespace C2.BSpec3

theorem golden_conjugate : ((1-Real.sqrt 5)/2) * ((1+Real.sqrt 5)/2) = -1 := by
  have h : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  nlinarith [h]
end C2.BSpec3

