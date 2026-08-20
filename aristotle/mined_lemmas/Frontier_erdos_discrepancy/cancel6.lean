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

private theorem cancel6 {a b c d e g : Int} (hab : b = -a) (hcd : d = -c)
    (hs : (a + b + c + d + e + g).natAbs ≤ 1)
    (he : e = 1 ∨ e = -1) (hg : g = 1 ∨ g = -1) : g = -e := by omega

