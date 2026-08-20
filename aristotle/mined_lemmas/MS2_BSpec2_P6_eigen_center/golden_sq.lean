import Mathlib
open Matrix Polynomial
namespace MS2.BSpec2

theorem golden_sq : ((1+Real.sqrt 5)/2)^2 = ((1+Real.sqrt 5)/2)+1 := by
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h]
end MS2.BSpec2

