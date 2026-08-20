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

def IsPMOne (f : Nat → Int) : Prop := ∀ n, 1 ≤ n → f n = 1 ∨ f n = -1

/-- **The Erdős discrepancy problem** (theorem of Tao): every `±1` sequence has
unbounded discrepancy along homogeneous arithmetic progressions, i.e. for every
bound `C` there are `d, n ≥ 1` with `|f d + f (2d) + ⋯ + f (nd)| > C`. -/
