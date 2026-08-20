import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma tangent_not_parallel (h : Indep3 A B C) (r : ℝ) :
    C - ⟪A, C⟫ • A ≠ r • (B - ⟪A, B⟫ • A) := by
  intro h0
  have key : (r * ⟪A, B⟫ - ⟪A, C⟫) • A + (-r) • B + (1 : ℝ) • C
      = (C - ⟪A, C⟫ • A) - r • (B - ⟪A, B⟫ • A) := by module
  rw [h0, sub_self] at key
  have := (h _ _ _ key).2.2
  norm_num at this

