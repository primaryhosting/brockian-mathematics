import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset

/-- A `±1` sequence, indexed by the positive integers. -/

theorem erdos_discrepancy (f : ℕ → ℤ) (hf : IsPlusMinusOne f) :
    ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ 2 ≤ |apSum f d n| := by
  obtain ⟨d, n, hd, hn, -, h⟩ := erdos_discrepancy_quantitative f hf
  exact ⟨d, n, hd, hn, h⟩

/-- The base case, phrased as the instance `C = 1` of the general statement. -/
