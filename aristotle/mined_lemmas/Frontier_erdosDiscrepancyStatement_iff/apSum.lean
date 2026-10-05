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

def apSum (f : ℕ → ℤ) (n d : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 n, f (i * d)

/-- The Erdős discrepancy statement (Tao's theorem): every `±1` sequence has
unbounded discrepancy along homogeneous arithmetic progressions. -/
