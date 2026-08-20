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

theorem isParadoxical_punctured_ball : IsParadoxical SO3 (Metric.closedBall (0 : E) 1 \ {0}) := by
  obtain ⟨P, Q, hP, hQ, hPQ, hsP, hsQ⟩ := isParadoxical_sph
  refine ⟨cone P, cone Q, ?_, ?_, cone_disjoint hPQ, ?_, ?_⟩
  · rw [← cone_sph]; exact cone_mono hP
  · rw [← cone_sph]; exact cone_mono hQ
  · rw [← cone_sph]; exact equidec_cone (fun _ hx => hx) hP hsP
  · rw [← cone_sph]; exact equidec_cone (fun _ hx => hx) hQ hsQ

/-! ### Absorbing the centre -/

/-- The centre of the auxiliary rotation axis, the point `(1/2, 0, 0)`. -/
