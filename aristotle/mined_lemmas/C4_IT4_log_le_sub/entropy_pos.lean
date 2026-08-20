import Mathlib
namespace C4.IT4

/-- The fundamental logarithm bound `log x ≤ x - 1` for positive `x`. -/

theorem entropy_pos (p : ℝ) (h0 : 0 < p) (h1 : p < 1) :
    0 < -p*Real.log p - (1-p)*Real.log (1-p) := by
  have hlp : Real.log p < 0 := Real.log_neg h0 h1
  have h0' : 0 < 1 - p := by linarith
  have h1' : 1 - p < 1 := by linarith
  have hlq : Real.log (1-p) < 0 := Real.log_neg h0' h1'
  nlinarith [mul_pos h0 (neg_pos.mpr hlp), mul_pos h0' (neg_pos.mpr hlq)]

/-- Gibbs' inequality for two-point distributions, as stated in the source file.  The
conclusion is `True`, so the statement holds trivially; see `gibbs_two'` below for the
substantive inequality. -/
