/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- A `±1`-sequence: a function `f : ℕ → ℤ` all of whose values on positive integers
are `1` or `-1`. -/

def FinitaryErdosDiscrepancyStatement : Prop :=
  ∀ C : ℕ, ∃ N : ℕ, ∀ f : ℕ → ℤ, IsPlusMinusOne f →
    ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ d * n ≤ N ∧ (C : ℤ) < |apSum f d n|

/-- If `a` and `b` are `±1` and `|a + b| ≤ 1`, then `b = -a`. -/
