import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma volume_wedgeC_split (hnC : nC ≠ 0) :
    volume {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, nA⟫ ∧ 0 ≤ ⟪x, nB⟫}
      = volume (Oct3 nA nB nC 1 1 1) + volume (Oct3 nA nB nC 1 1 (-1)) := by
  have e1 : {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, nA⟫ ∧ 0 ≤ ⟪x, nB⟫} ∩ {x | 0 ≤ (1 : ℝ) * ⟪x, nC⟫}
      = Oct3 nA nB nC 1 1 1 := by
    ext x
    simp only [Oct3, Oct2, Oct1, unitBall3, mem_inter_iff, mem_setOf_eq, one_mul]
    tauto
  have e2 : {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ ⟪x, nA⟫ ∧ 0 ≤ ⟪x, nB⟫} ∩ {x | 0 ≤ (-1 : ℝ) * ⟪x, nC⟫}
      = Oct3 nA nB nC 1 1 (-1) := by
    ext x
    simp only [Oct3, Oct2, Oct1, unitBall3, mem_inter_iff, mem_setOf_eq, one_mul]
    tauto
  rw [volume_split' _ (measurableSet_wedge nA nB) nC hnC, e1, e2]

end

end Math

import RequestProject.Defs

/-!
# The volume of a wedge of the unit ball

The main result of this file is `Math.volume_wedge`: the part of the closed unit ball of
`E3` cut out by two half-spaces through the origin with unit normals `m`, `n` has volume
`2 * (π - angle m n) / 3`; equivalently, the corresponding "lune" of the unit sphere,
whose dihedral angle is `π - angle m n`, has area twice its angle.
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- `∫_0^1 2 r √(1-r²) dr = 2/3`. -/
