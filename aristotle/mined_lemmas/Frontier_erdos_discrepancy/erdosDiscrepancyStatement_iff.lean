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

theorem erdosDiscrepancyStatement_iff :
    ErdosDiscrepancyStatement ↔ ∀ f : ℕ → ℤ, IsPMOne f → UnboundedDiscrepancy f := Iff.rfl

/-! ### Sequences that are eventually constant along a progression -/

/-- A homogeneous sum of `n` terms of a `±1` sequence has absolute value at most `n`. -/
