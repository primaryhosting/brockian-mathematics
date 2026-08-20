import Mathlib
namespace C4.RA7

/-- Triangle inequality for the absolute value on `ℝ` (Mathlib: `abs_add_le`). -/

theorem abs_triangle (a b : ℝ) : |a + b| ≤ |a| + |b| := abs_add_le a b

/-- Squares of reals are nonnegative (Mathlib: `sq_nonneg`). -/
