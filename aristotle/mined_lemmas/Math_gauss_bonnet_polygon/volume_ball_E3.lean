import RequestProject.Sector

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- Euclidean three-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The volume of the standard solid wedge of dihedral angle `psi` inside the unit ball:
the axis of the wedge is the first coordinate axis, and the wedge is described in the plane
of the last two coordinates as the cone spanned by `(1,0)` and `(cos psi, sin psi)`. -/

theorem volume_ball_E3 : volume (ball (0 : E3) 1) = ENNReal.ofReal (4 * π / 3) := by
  rw [EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, one_pow, ENNReal.ofReal_one, one_mul]
  congr 1
  rw [show ((3 : ℕ) : ℝ) / 2 + 1 = 3 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq, show Real.sqrt π ^ 3 = π * Real.sqrt π by
      rw [pow_succ, Real.sq_sqrt Real.pi_nonneg]]
  have hpos : Real.sqrt π > 0 := Real.sqrt_pos.2 Real.pi_pos
  field_simp
  ring

