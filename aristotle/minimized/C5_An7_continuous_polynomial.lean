import Mathlib
namespace C5.An7

theorem continuous_polynomial (a b c : ℝ) : Continuous (fun x : ℝ => a*x^2 + b*x + c) := by
  fun_prop
