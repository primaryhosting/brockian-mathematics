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

theorem finitary_erdos_discrepancy_C_one (f : ℕ → ℤ) (hf : IsPlusMinusOne f) :
    ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ d * n ≤ 12 ∧ ((1 : ℕ) : ℤ) < |apSum f d n| := by
  obtain ⟨d, n, hd, hn, hdn, hs⟩ := erdos_discrepancy f hf
  exact ⟨d, n, hd, hn, hdn, by push_cast; omega⟩

open Filter in
/-- **A Lean-checked reduction: the Erdős discrepancy statement is equivalent to its
finitary form.** The nontrivial direction is a compactness argument: from a sequence of
counterexamples on longer and longer initial segments one extracts, along a nonprincipal
ultrafilter, a single `±1`-sequence of bounded discrepancy. -/
