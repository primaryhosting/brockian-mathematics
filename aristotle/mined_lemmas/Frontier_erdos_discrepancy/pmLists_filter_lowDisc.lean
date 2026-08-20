import Mathlib
import RequestProject.ErdosDiscrepancy
import RequestProject.ErdosDiscrepancyMathlib
import RequestProject.ErdosDiscrepancySpecialCases
import RequestProject.ErdosDiscrepancyMeasure

/-!
# The base case for completely multiplicative sequences

For a completely multiplicative `±1` sequence every homogeneous sum is `f d` times an
ordinary partial sum, so only the sums `S n = f 1 + ⋯ + f n` matter.  Tracking the four
values `f 2, f 3, f 5, f 7` shows that one of `S 4, S 6, S 8, S 10` must exceed `1` in
absolute value: for completely multiplicative sequences the length `10` already forces
discrepancy `2` (as opposed to `12` in general).
-/

namespace Frontier

/-- Unfolding the ordinary partial sums. -/

theorem pmLists_filter_lowDisc :
    (pmLists 11).filter lowDisc =
      [[1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1],
       [-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, 1],
       [1, -1, -1, 1, -1, 1, 1, -1, -1, 1, -1],
       [-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1]] := by
  decide +kernel

/-- **Classification.**  A `±1` sequence with discrepancy `1` on every homogeneous
progression inside `{1, …, 11}` has one of exactly four patterns of initial values. -/
