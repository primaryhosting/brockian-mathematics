import Mathlib
open Finset
namespace MS2.IT2


theorem log_sum_two (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.log (a*b) = Real.log a + Real.log b :=
  Real.log_mul ha.ne' hb.ne'

