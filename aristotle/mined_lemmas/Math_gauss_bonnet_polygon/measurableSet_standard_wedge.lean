import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma measurableSet_standard_wedge (ψ : ℝ) : MeasurableSet
    {y : EuclideanSpace ℝ (Fin 3) | ‖y‖ ≤ 1 ∧ 0 ≤ y 0 ∧ 0 ≤ cos ψ * y 0 + sin ψ * y 1} := by
  have hnm : Measurable fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖ := by fun_prop
  have hc0 : Measurable fun y : EuclideanSpace ℝ (Fin 3) => y 0 :=
    (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) => y 0).measurable
  have hc1 : Measurable fun y : EuclideanSpace ℝ (Fin 3) => y 1 :=
    (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) => y 1).measurable
  exact (measurableSet_le hnm measurable_const).inter
      ((measurableSet_le measurable_const hc0).inter
        (measurableSet_le measurable_const
          ((measurable_const.mul hc0).add (measurable_const.mul hc1))))

/-- Any pair of orthonormal vectors of `E3` extends to an orthonormal basis. -/
