import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

noncomputable def normalTo (A B C : E3) : E3 :=
  (C - ⟪A, C⟫ • A) - (⟪C - ⟪A, C⟫ • A, B - ⟪A, B⟫ • A⟫ / ⟪B - ⟪A, B⟫ • A, B - ⟪A, B⟫ • A⟫) •
    (B - ⟪A, B⟫ • A)

end Math

import RequestProject.Defs

/-!
# Normals to the sides of a spherical triangle, and the dihedral angle identity
-/

namespace Math

open MeasureTheory Metric Real Module InnerProductGeometry
open scoped RealInnerProductSpace

/-- A convenient form of linear independence for three vectors. -/
