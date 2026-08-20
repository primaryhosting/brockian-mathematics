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

theorem erdosDiscrepancyStatement_iff_uniform :
    ErdosDiscrepancyStatement ↔
      ∀ C : ℕ, ∃ N : ℕ, ∀ f : ℕ → ℤ, IsPMOne f → C < discrepancyUpTo f N :=
  erdos_iff_finite.trans finiteErdosStatement_iff_discrepancyUpTo

end Frontier

import Mathlib
import RequestProject.ErdosDiscrepancy
import RequestProject.ErdosDiscrepancyMathlib
import RequestProject.ErdosDiscrepancySpecialCases
import RequestProject.ErdosDiscrepancyMeasure

/-!
# Two remarks on the shape of the statement

* **A single progression is not enough.**  The alternating sequence has all its ordinary
  partial sums in `{0, 1}`, so the discrepancy along the progression of difference `1`
  stays bounded forever; the Erdős discrepancy statement really uses all differences `d`
  at once.  (Consistently with this, the alternating sequence is periodic, hence has
  unbounded discrepancy overall by `Frontier.unboundedDiscrepancy_of_periodic`: the
  progression of difference `2` is constant.)

* **Dilation.**  Replacing `f` by `n ↦ f (k * n)` turns the progression of difference `d`
  into the progression of difference `k * d`, so a dilation cannot have larger discrepancy
  than the original sequence (up to rescaling the length bound).
-/

namespace Frontier

/-! ### The alternating sequence -/

/-- The alternating `±1` sequence `1, -1, 1, -1, …`. -/
