import Mathlib
namespace Frontier.BrockianNextLevel

theorem golden_fixed_point : ((1 + Real.sqrt 5)/2)^2 = ((1 + Real.sqrt 5)/2) + 1 := by
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h]
end Frontier.BrockianNextLevel

