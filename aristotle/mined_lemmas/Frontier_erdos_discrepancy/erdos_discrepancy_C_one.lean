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

theorem erdos_discrepancy_C_one (f : ℕ → ℤ) (hf : IsPlusMinusOne f) :
    ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ ((1 : ℕ) : ℤ) < |apSum f d n| := by
  obtain ⟨d, n, hd, hn, -, hs⟩ := erdos_discrepancy f hf
  exact ⟨d, n, hd, hn, by push_cast; omega⟩

/-- The `C = 1` instance of the finitary statement holds with the (optimal) bound
`N = 12`. -/
