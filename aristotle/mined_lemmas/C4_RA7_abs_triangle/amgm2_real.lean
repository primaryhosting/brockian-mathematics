import Mathlib
namespace C4.RA7

/-- Triangle inequality for the absolute value on `ℝ` (Mathlib: `abs_add_le`). -/

theorem amgm2_real (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 2 * Real.sqrt (a*b) ≤ a + b := by
  rw [Real.sqrt_mul ha]
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb]

end C4.RA7

