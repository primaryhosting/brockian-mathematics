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

def apSum (f : ℕ → ℤ) (n d : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 n, f (i * d)

/-- The Erdős discrepancy statement (Tao's theorem): every `±1` sequence has
unbounded discrepancy along homogeneous arithmetic progressions. -/

def ErdosDiscrepancyStatement : Prop :=
  ∀ f : ℕ → ℤ, IsPMOne f → ∀ C : ℤ, ∃ n d : ℕ, 0 < n ∧ 0 < d ∧ C < |apSum f n d|

/-- Reduction: the Erdős discrepancy statement is equivalent to saying that no
`±1` sequence has discrepancy bounded by some constant `C`. -/

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
