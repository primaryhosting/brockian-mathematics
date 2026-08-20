import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma volume_wedgeA_split (hnA : nA ≠ 0) :
    volume {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, nB⟫ ∧ 0 ≤ ⟪x, nC⟫}
      = volume (Oct3 nA nB nC 1 1 1) + volume (Oct3 nA nB nC (-1) 1 1) := by
  have e1 : {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, nB⟫ ∧ 0 ≤ ⟪x, nC⟫} ∩ {x | 0 ≤ (1 : ℝ) * ⟪x, nA⟫}
      = Oct3 nA nB nC 1 1 1 := by
    ext x
    simp only [Oct3, Oct2, Oct1, unitBall3, mem_inter_iff, mem_setOf_eq, one_mul]
    tauto
  have e2 : {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, nB⟫ ∧ 0 ≤ ⟪x, nC⟫} ∩ {x | 0 ≤ (-1 : ℝ) * ⟪x, nA⟫}
      = Oct3 nA nB nC (-1) 1 1 := by
    ext x
    simp only [Oct3, Oct2, Oct1, unitBall3, mem_inter_iff, mem_setOf_eq, one_mul]
    tauto
  rw [volume_split' _ (measurableSet_wedge nB nC) nA hnA, e1, e2]

/-- The wedge at the vertex `B` splits into two octants. -/
