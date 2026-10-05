/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Frontier

/-- `f` is a `±1`-valued sequence (only the positive indices matter). -/

theorem pm_add_eq_neg (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (h : |a + b| < 2) : b = -a := by
  rw [abs_lt] at h
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> omega

end Helpers

/-- **Base case of the Erdős discrepancy problem** (`C = 1`): no `±1` sequence
has discrepancy at most `1` along homogeneous arithmetic progressions.  Every
`±1` sequence admits a homogeneous arithmetic progression on which the sum has
absolute value at least `2`. -/
