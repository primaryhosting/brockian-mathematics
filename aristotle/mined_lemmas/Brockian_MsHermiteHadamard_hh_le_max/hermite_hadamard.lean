import Mathlib
namespace Brockian.MsHermiteHadamard

open MeasureTheory Set

/-- A convex function on `[a,b]` is bounded above by the max of its values at the endpoints. -/

theorem hermite_hadamard (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ConvexOn ℝ (Set.Icc a b) f) :
    f ((a + b) / 2) ≤ (1 / (b - a)) * ∫ x in a..b, f x ∧
    (1 / (b - a)) * ∫ x in a..b, f x ≤ (f a + f b) / 2 := by
  have hba : (0:ℝ) < b - a := by linarith
  constructor
  · rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hba, mul_comm]
    exact hh_left hab hf
  · rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hba, mul_comm]
    exact hh_right hab hf

end Brockian.MsHermiteHadamard

