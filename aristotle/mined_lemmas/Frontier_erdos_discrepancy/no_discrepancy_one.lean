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

private theorem no_discrepancy_one {a1 a2 a3 a4 a6 a9 a10 a12 : Int}
    (v1 : a1 = 1 ∨ a1 = -1) (p12 : a2 = -a1) (p34 : a4 = -a3) (q24 : a4 = -a2)
    (r36 : a6 = -a3) (s612 : a12 = -a6) (r912 : a12 = -a9)
    (p910 : a10 = -a9) (q1012 : a12 = -a10) : False := by omega

/-- **Erdős discrepancy, the base case `C = 1`, in finitary form.**
For every `±1` sequence there are `d, n ≥ 1` with `n * d ≤ 12` and
`|f d + f (2d) + ⋯ + f (nd)| > 1`; that is, discrepancy at least `2` is already
forced by the twelve values `f 1, …, f 12`. -/
