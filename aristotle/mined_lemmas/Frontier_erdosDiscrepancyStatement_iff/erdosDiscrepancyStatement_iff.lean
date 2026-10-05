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

theorem erdosDiscrepancyStatement_iff :
    ErdosDiscrepancyStatement ↔
      ∀ f : ℕ → ℤ, IsPMOne f → ∀ C : ℤ,
        ¬ (∀ n d : ℕ, 0 < n → 0 < d → |apSum f n d| ≤ C) := by
  constructor
  · intro h f hf C hC
    obtain ⟨n, d, hn, hd, hlt⟩ := h f hf C
    exact absurd (hC n d hn hd) (not_le.2 hlt)
  · intro h f hf C
    by_contra hcon
    push_neg at hcon
    exact h f hf C fun n d hn hd => hcon n d hn hd

section Helpers

variable {a b : ℤ}

/-- If `a, b ∈ {±1}` and `|a + b| < 2`, then `b = -a`. -/
