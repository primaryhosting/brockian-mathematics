import Mathlib
open Matrix Polynomial
namespace C4.BSp5

theorem golden_recip : ((1+Real.sqrt 5)/2)⁻¹ = ((Real.sqrt 5 - 1)/2) := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : (1 + Real.sqrt 5) / 2 ≠ 0 := by positivity
  field_simp
  nlinarith [h5]

end C4.BSp5

