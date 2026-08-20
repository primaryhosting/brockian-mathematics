/-
Absorbing the countable set of poles: the unit sphere is `SO(3)`-paradoxical.
-/
import RequestProject.Sphere

open Matrix Set Pointwise

namespace BT

noncomputable section

/-! ### Countability of the solution sets of rotation equations -/

/-- For a point `d` off the `z`-axis, only countably many angles `t` satisfy
`rZ (c * t) • d = d'`. -/

theorem isParadoxical_ball : IsParadoxical Iso3 (Metric.closedBall (0 : E) 1) :=
  IsParadoxical.of_equidec (Equidec.symm equidec_ball_punctured)
    (isParadoxical_iso3_of_so3 isParadoxical_punctured_ball)

end

end BT

/-
The Hausdorff paradox: the unit sphere in `ℝ³` is `SO(3)`-paradoxical.
-/
import RequestProject.FreeRotations

open Matrix Set Pointwise

namespace BT

noncomputable section

/-- Euclidean 3-space. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-! ### `SO(3)` acts by isometries -/

