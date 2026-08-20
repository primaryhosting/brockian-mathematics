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

theorem finite_erdos_base_case :
    ∃ N : ℕ, ∀ f : ℕ → ℤ, IsPMOne f →
      ∃ d n : ℕ, 1 ≤ d ∧ 1 ≤ n ∧ n * d ≤ N ∧ 1 < (homogSum f d n).natAbs :=
  ⟨12, erdos_discrepancy_le_twelve⟩

end Frontier

import Mathlib
import RequestProject.ErdosDiscrepancy
import RequestProject.ErdosDiscrepancyMathlib
import RequestProject.ErdosDiscrepancyCompactness

/-!
# Classification of the discrepancy-one sequences of length eleven

`Frontier.erdos_discrepancy_le_twelve` shows that no `±1` sequence has discrepancy `1`
on all homogeneous progressions inside `{1, …, 12}`, and `Frontier.goodSeq` shows that
this fails for `11`.  Here we classify *all* the exceptional patterns: there are exactly
four `±1` patterns of length `11` with discrepancy `1`, namely two patterns and their
negatives; they agree on `{1, …, 10}` up to sign and are free at `11`.

The enumeration is a finite kernel computation over the `2 ^ 11` patterns.
-/

namespace Frontier

/-- All `±1` patterns of a given length. -/
