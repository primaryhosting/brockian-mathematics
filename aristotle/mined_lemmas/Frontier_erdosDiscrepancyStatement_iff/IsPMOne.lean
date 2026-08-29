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

def IsPMOne (f : ℕ → ℤ) : Prop := ∀ n, 1 ≤ n → f n = 1 ∨ f n = -1

/-- The discrepancy sum of `f` along the homogeneous arithmetic progression with
common difference `d` and length `n`, i.e. `f d + f (2d) + ⋯ + f (n d)`. -/
