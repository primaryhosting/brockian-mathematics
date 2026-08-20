import Mathlib
open Finset
namespace C2.IT3

/-- Each entropy term `-p log p` is nonnegative on `[0,1]`. -/

theorem log_concave (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.log ((x+y)/2) ≥ (Real.log x + Real.log y)/2 := by
  have hs : Real.sqrt (x*y) ≤ (x+y)/2 := by
    nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ x*y), Real.sqrt_nonneg (x*y),
      sq_nonneg (Real.sqrt (x*y) - x), sq_nonneg (x - y)]
  have h1 : Real.log (Real.sqrt (x*y)) = (Real.log x + Real.log y)/2 := by
    rw [Real.log_sqrt (by positivity), Real.log_mul (ne_of_gt hx) (ne_of_gt hy)]
  rw [← h1]
  exact Real.log_le_log (by positivity) hs

end C2.IT3

