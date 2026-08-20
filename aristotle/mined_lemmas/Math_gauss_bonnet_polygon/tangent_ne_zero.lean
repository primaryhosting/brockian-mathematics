import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma tangent_ne_zero (h : Indep3 A B C) : B - ⟪A, B⟫ • A ≠ 0 := by
  intro h0
  have key : ⟪A, B⟫ • A + (-1 : ℝ) • B + (0 : ℝ) • C = -(B - ⟪A, B⟫ • A) := by module
  rw [h0, neg_zero] at key
  have := (h _ _ _ key).2.1
  norm_num at this

/-- The two tangent directions at `A` are not parallel. -/
