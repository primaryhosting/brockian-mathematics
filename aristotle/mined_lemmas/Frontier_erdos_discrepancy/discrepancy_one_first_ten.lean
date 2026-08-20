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

theorem discrepancy_one_first_ten (f : ℕ → ℤ) (hf : IsPMOne f)
    (h : ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → n * d ≤ 11 → (homogSum f d n).natAbs ≤ 1) :
    [f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10] = [1, -1, -1, 1, -1, 1, 1, -1, -1, 1] ∨
    [f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10] =
      [-1, 1, 1, -1, 1, -1, -1, 1, 1, -1] := by
  have := discrepancy_one_classification f hf h
  simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq] at this
  rcases this with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ |
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ |
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ |
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ <;>
    simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

end Frontier

import Mathlib
import RequestProject.ErdosDiscrepancy
import RequestProject.ErdosDiscrepancyMathlib

/-!
# Special cases and reductions for the Erdős discrepancy problem

We record:

* `Frontier.UnboundedDiscrepancy`, the per-sequence form of the statement, and the fact
  that the Erdős discrepancy statement is exactly "every `±1` sequence has unbounded
  discrepancy";
* the theorem for all sequences that are **eventually constant along some homogeneous
  progression** (the sums along that progression then grow linearly), and its corollaries
  for **eventually periodic** and **periodic** `±1` sequences;
* the reduction for **completely multiplicative** `±1` sequences: all homogeneous sums are
  of the form `f d * (f 1 + ⋯ + f n)`, so unbounded discrepancy is equivalent to
  unboundedness of the ordinary partial sums.
-/

namespace Frontier

/-- `f` has unbounded discrepancy along homogeneous arithmetic progressions. -/
