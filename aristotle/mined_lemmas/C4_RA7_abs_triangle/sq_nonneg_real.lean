import Mathlib
namespace C4.RA7

/-- Triangle inequality for the absolute value on `ℝ` (Mathlib: `abs_add_le`). -/

theorem sq_nonneg_real (a : ℝ) : 0 ≤ a^2 := sq_nonneg a

/-- AM–GM for two nonnegative reals: `2√(ab) ≤ a + b`. -/
