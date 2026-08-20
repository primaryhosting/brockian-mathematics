import Mathlib
namespace C6.BD6

/-- `Real.sqrt 5` squared is `5`. -/

theorem golden_pow5 : ((1+Real.sqrt 5)/2)^5 = 5*((1+Real.sqrt 5)/2) + 3 := by
  linear_combination
    ((Real.sqrt 5 ^ 3 + 5 * Real.sqrt 5 ^ 2 + 15 * Real.sqrt 5 + 35) / 32) * sq_sqrt_five

