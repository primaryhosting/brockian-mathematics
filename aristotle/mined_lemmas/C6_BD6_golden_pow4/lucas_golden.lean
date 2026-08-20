import Mathlib
namespace C6.BD6

/-- `Real.sqrt 5` squared is `5`. -/

theorem lucas_golden : ((1+Real.sqrt 5)/2)^3 + ((1-Real.sqrt 5)/2)^3 = 4 := by
  linear_combination (3/4 : ℝ) * sq_sqrt_five

end C6.BD6

