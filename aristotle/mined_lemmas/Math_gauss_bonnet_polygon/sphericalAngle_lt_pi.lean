import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma sphericalAngle_lt_pi (h : Indep3 A B C) : sphericalAngle A B C < π := by
  rcases lt_or_eq_of_le (angle_le_pi (B - ⟪A, B⟫ • A) (C - ⟪A, C⟫ • A)) with h' | h'
  · exact h'
  · exfalso
    rw [angle_eq_pi_iff] at h'
    obtain ⟨-, r, -, hr⟩ := h'
    exact tangent_not_parallel h r hr

/-- The angle between the two side normals at the vertex `A` is supplementary to the
interior angle of the triangle at `A`. -/
