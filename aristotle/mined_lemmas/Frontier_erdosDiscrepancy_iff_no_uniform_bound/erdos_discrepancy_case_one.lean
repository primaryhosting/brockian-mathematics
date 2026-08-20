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

theorem erdos_discrepancy_case_one (f : ℕ → ℤ) (hf : IsPlusMinusOne f) :
    ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ (1 : ℤ) < |apSum f d n| := by
  obtain ⟨d, n, hd, hn, h⟩ := erdos_discrepancy f hf
  exact ⟨d, n, hd, hn, by omega⟩

/-- Dilation reduction: for every `k ≥ 1`, the dilated sequence `n ↦ f (k * n)` is again
a `±1` sequence, so the base case applies to it: the discrepancy bound `2` is attained on
homogeneous APs whose common difference is a multiple of `k`. -/
