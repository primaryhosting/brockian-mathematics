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

theorem triSum_triIdx (k : ℕ) : triSum (triIdx k) = k + 1 := by
  induction k with
  | zero => rw [show triIdx 0 = 1 from rfl, triSum, homogSum]; norm_num [triSeq_mod_one]
  | succ j ih =>
      have hstep : triIdx (j + 1) = 3 * triIdx j + 1 := rfl
      rw [hstep, triSum_three_mul_add_one, ih]
      push_cast
      ring

/-- **The base-`3` sequence has unbounded discrepancy** (in fact logarithmically growing:
the partial sum at `(3 ^ (k+1) - 1) / 2` equals `k + 1`). -/
