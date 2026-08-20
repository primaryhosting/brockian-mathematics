import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma sphericalAngle_pos (h : Indep3 A B C) : 0 < sphericalAngle A B C := by
  rcases lt_or_eq_of_le (angle_nonneg (B - ⟪A, B⟫ • A) (C - ⟪A, C⟫ • A)) with h' | h'
  · exact h'
  · exfalso
    rw [eq_comm, angle_eq_zero_iff] at h'
    obtain ⟨-, r, -, hr⟩ := h'
    exact tangent_not_parallel h r hr

