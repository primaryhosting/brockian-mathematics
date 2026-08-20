import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

noncomputable def sphericalAngle (A B C : E3) : ℝ :=
  InnerProductGeometry.angle (B - ⟪A, B⟫ • A) (C - ⟪A, C⟫ • A)

/-- `normalTo A B C` is the component of `C` orthogonal to the plane spanned by `A` and `B`
(for unit `A`); it is orthogonal to `A` and `B` and has positive inner product with `C`. -/
