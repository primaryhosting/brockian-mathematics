import RequestProject.Sector

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The volume of the standard solid wedge of dihedral angle `psi` inside the unit ball:
the axis of the wedge is the first coordinate axis, and the wedge is described in the plane
of the last two coordinates as the cone spanned by `(1,0)` and `(cos psi, sin psi)`. -/

theorem sphericalArea_eq_toSphere (S : Set (sphere (0 : E3) 1)) (hS : MeasurableSet S) :
    ENNReal.ofReal (sphericalArea (Subtype.val '' S)) = volume.toSphere S := by
  have hsub : (Subtype.val '' S : Set E3) ⊆ sphere 0 1 := by
    rintro _ ⟨x, hx, rfl⟩; exact x.2
  have hfin : volume (Ioo (0 : ℝ) 1 • (Subtype.val '' S : Set E3)) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (cone_subset_ball _ hsub))
  rw [Measure.toSphere_apply' _ hS, sphericalArea, ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_toReal hfin]
  norm_num

/-! ## The Gauss-Bonnet theorem for a spherical triangle -/

/-- **Girard's theorem** (the Gauss-Bonnet theorem for a geodesic triangle on the unit
sphere): the sum of the angles of a geodesic triangle on the unit sphere exceeds `π` by
exactly the area of the triangle. -/
