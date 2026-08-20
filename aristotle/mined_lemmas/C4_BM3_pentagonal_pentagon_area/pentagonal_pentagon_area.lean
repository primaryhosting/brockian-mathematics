import Mathlib
namespace C4.BM3


theorem pentagonal_pentagon_area : (5:ℝ) * Real.sin (2*Real.pi/5) / 2 > 0 := by
  have hpi := Real.pi_pos
  have hs : Real.sin (2*Real.pi/5) > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith
  positivity

