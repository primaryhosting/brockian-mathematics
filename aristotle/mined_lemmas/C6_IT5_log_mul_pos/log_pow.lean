import Mathlib
namespace C6.IT5

/-- The logarithm of a product of positive reals is the sum of the logarithms.
(`Real.log_mul` in Mathlib, which only needs nonvanishing.) -/

theorem log_pow (a : ℝ) (ha : 0 < a) (n : ℕ) : Real.log (a^n) = n * Real.log a :=
  Real.log_pow a n

/-- The exponential turns sums into products (`Real.exp_add`). -/
