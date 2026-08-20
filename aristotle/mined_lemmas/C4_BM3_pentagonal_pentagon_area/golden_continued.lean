import Mathlib
namespace C4.BM3


theorem golden_continued : ((1+Real.sqrt 5)/2) = 1 + 1/((1+Real.sqrt 5)/2) := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num)
  have hne : (1 + Real.sqrt 5)/2 ≠ 0 := by positivity
  field_simp
  nlinarith [h5]

