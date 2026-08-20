import Mathlib
namespace C4.IT4

/-- The fundamental logarithm bound `log x ≤ x - 1` for positive `x`. -/

theorem log_le_sub (x : ℝ) (hx : 0 < x) : Real.log x ≤ x - 1 :=
  Real.log_le_sub_one_of_pos hx

/-- The binary entropy is strictly positive strictly between `0` and `1`. -/
