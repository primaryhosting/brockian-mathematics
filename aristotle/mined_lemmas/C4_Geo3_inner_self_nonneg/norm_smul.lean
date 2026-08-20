import Mathlib
namespace C4.Geo3

/-- The inner product of a vector with itself is nonnegative. -/

theorem norm_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (c : ℝ) (a : V) :
    ‖c • a‖ = |c| * ‖a‖ := by
  rw [_root_.norm_smul, Real.norm_eq_abs]

/-- The Cauchy–Schwarz inequality in a real inner product space. -/
