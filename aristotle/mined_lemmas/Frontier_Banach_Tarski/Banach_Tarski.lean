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

theorem Banach_Tarski :
    ∃ P Q : Set (EuclideanSpace ℝ (Fin 3)),
      P ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ∧
      Q ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ∧
      Disjoint P Q ∧
      BT.Equidec (EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3))
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) P ∧
      BT.Equidec (EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3))
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) Q :=
  BT.isParadoxical_ball

end Frontier

