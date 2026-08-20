import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma measurableSet_wedge (m n : E3) :
    MeasurableSet {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, m⟫ ∧ 0 ≤ ⟪x, n⟫} := by
  rw [wedge_eq_inter]
  exact (measurableSet_unitBall3.inter (measurableSet_halfspace 1 m)).inter
    (measurableSet_halfspace 1 n)

/-- The wedge at the vertex `A` splits into two octants. -/
