import Mathlib
namespace C6.BD6

/-- `Real.sqrt 5` squared is `5`. -/

private lemma sq_sqrt_five : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

theorem golden_pow4 : ((1+Real.sqrt 5)/2)^4 = 3*((1+Real.sqrt 5)/2) + 2 := by
  linear_combination ((Real.sqrt 5 ^ 2 + 4 * Real.sqrt 5 + 11) / 16) * sq_sqrt_five
