import RequestProject.Sector

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The volume of the standard solid wedge of dihedral angle `psi` inside the unit ball:
the axis of the wedge is the first coordinate axis, and the wedge is described in the plane
of the last two coordinates as the cone spanned by `(1,0)` and `(cos psi, sin psi)`. -/

theorem sin_angle_pos (p q : E3) (hpq : LinearIndependent ℝ ![p, q]) :
    0 < Real.sin (angle p q) := by
  have hpq' := LinearIndependent.pair_iff.1 hpq
  refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
  · rcases (angle_nonneg p q).lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨-, r, hr, hqr⟩ := angle_eq_zero_iff.1 h.symm
      have := hpq' r (-1) (by rw [hqr]; module)
      linarith [this.2]
  · rcases (angle_le_pi p q).lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨-, r, hr, hqr⟩ := angle_eq_pi_iff.1 h
      have := hpq' r (-1) (by rw [hqr]; module)
      linarith [this.2]

/-- An orthonormal frame adapted to a wedge: `b1` is the direction of `p`, and `b2` is the
direction of the component of `q` orthogonal to `p`. -/
