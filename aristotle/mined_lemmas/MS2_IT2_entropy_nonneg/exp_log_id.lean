import Mathlib
open Finset
namespace MS2.IT2


theorem exp_log_id (x : ℝ) (hx : 0 < x) : Real.exp (Real.log x) = x := Real.exp_log hx

end MS2.IT2

