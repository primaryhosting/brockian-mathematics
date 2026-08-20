import Mathlib
namespace C6.IT5

/-- The logarithm of a product of positive reals is the sum of the logarithms.
(`Real.log_mul` in Mathlib, which only needs nonvanishing.) -/

theorem log_mul_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.log (a*b) = Real.log a + Real.log b :=
  Real.log_mul ha.ne' hb.ne'

/-- `log (a ^ n) = n * log a` for a natural power (`Real.log_pow`; the positivity
hypothesis is not needed, but is kept as requested). -/
