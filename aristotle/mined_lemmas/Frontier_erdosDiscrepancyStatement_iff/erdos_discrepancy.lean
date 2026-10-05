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

theorem erdos_discrepancy (f : ℕ → ℤ) (hf : IsPMOne f) :
    ∃ n d : ℕ, 0 < n ∧ 0 < d ∧ (1 : ℤ) < |apSum f n d| := by
  obtain ⟨n, d, hn, hd, h⟩ := erdos_discrepancy_base f hf
  exact ⟨n, d, hn, hd, by omega⟩

end Frontier

