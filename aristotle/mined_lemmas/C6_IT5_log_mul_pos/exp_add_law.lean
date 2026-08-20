import Mathlib
namespace C6.IT5

/-- The logarithm of a product of positive reals is the sum of the logarithms.
(`Real.log_mul` in Mathlib, which only needs nonvanishing.) -/

theorem exp_add_law (a b : ℝ) : Real.exp (a+b) = Real.exp a * Real.exp b :=
  Real.exp_add a b

end C6.IT5

