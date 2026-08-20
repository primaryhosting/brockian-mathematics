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

theorem homogSum_altSeq_one (n : ℕ) :
    homogSum altSeq 1 n = if n % 2 = 1 then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [homogSum_succ, mul_one, ih]
      by_cases h : m % 2 = 1
      · have h' : (m + 1) % 2 = 0 := by omega
        simp [h, h', altSeq]
      · have h' : (m + 1) % 2 = 1 := by omega
        simp [h, h', altSeq]

/-- Along the progression of difference `1` the alternating sequence has discrepancy `1`
for every length: unboundedness in the Erdős discrepancy problem genuinely requires
varying the common difference. -/
