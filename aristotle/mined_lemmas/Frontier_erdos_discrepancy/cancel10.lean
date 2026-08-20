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

private theorem cancel10 {a b c d e g h i j k : Int} (hab : b = -a) (hcd : d = -c) (heg : g = -e)
    (hhi : i = -h) (hs : (a + b + c + d + e + g + h + i + j + k).natAbs ≤ 1)
    (hj : j = 1 ∨ j = -1) (hk : k = 1 ∨ k = -1) : k = -j := by omega

/-- The eleven cancellation relations forced by a discrepancy-`1` sequence are
contradictory. -/
