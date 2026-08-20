import Mathlib
open Finset
namespace Frontier.AnalysisCalculus


theorem am_gm_two (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : Real.sqrt (a*b) ≤ (a+b)/2 := by
  rw [show (a+b)/2 = Real.sqrt (((a+b)/2)^2) by rw [Real.sqrt_sq (by linarith)]]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (a-b)]

