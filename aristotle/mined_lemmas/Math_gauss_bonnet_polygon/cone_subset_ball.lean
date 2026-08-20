import RequestProject.Sector

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The volume of the standard solid wedge of dihedral angle `psi` inside the unit ball:
the axis of the wedge is the first coordinate axis, and the wedge is described in the plane
of the last two coordinates as the cone spanned by `(1,0)` and `(cos psi, sin psi)`. -/

theorem cone_subset_ball (S : Set E3) (hS : S ⊆ sphere 0 1) : Ioo (0 : ℝ) 1 • S ⊆ ball 0 1 := by
  rintro _ ⟨t, ht, x, hx, rfl⟩
  have hx1 : ‖x‖ = 1 := by simpa using hS hx
  simp [norm_smul, hx1, abs_of_pos ht.1, ht.2]

/-! ### Solid lunes and octants cut out by half spaces -/

/-- The solid lune of the unit ball determined by two linear functionals. -/
