import RequestProject.Sector

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The volume of the standard solid wedge of dihedral angle `psi` inside the unit ball:
the axis of the wedge is the first coordinate axis, and the wedge is described in the plane
of the last two coordinates as the cone spanned by `(1,0)` and `(cos psi, sin psi)`. -/

theorem volume_octant_neg (k l m : E3 →ₗ[ℝ] ℝ) :
    volume (octant (-k) (-l) (-m)) = volume (octant k l m) := by
  have : octant (-k) (-l) (-m) = (fun x : E3 => -x) ⁻¹' octant k l m := by
    ext x
    simp only [octant, lune, mem_inter_iff, mem_setOf_eq, mem_preimage, LinearMap.neg_apply,
      map_neg, mem_ball_zero_iff, norm_neg]
  rw [this, Measure.measure_preimage_neg]

/-- The volume of the solid lune cut out by the two half spaces spanned by `u, w` and by
`v, w`: it is `2/3` times the angle of the spherical triangle at the vertex `w`. -/
