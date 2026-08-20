import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma wedge_eq_inter (m n : E3) :
    {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, m⟫ ∧ 0 ≤ ⟪x, n⟫}
      = unitBall3 ∩ {x | 0 ≤ (1 : ℝ) * ⟪x, m⟫} ∩ {x | 0 ≤ (1 : ℝ) * ⟪x, n⟫} := by
  ext x
  simp only [unitBall3, mem_inter_iff, mem_setOf_eq, one_mul]
  tauto

