/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is written in plain Lean 4 core (no imports), so that the header comment above
can legally be the very first thing in the file.
-/

namespace Frontier

/-- A `±1` sequence: `f n ∈ {1, -1}` for every index `n ≥ 1`. -/

theorem erdos_discrepancy_of_le_one (f : Nat → Int) (hf : IsPlusMinusOne f) (C : Nat)
    (hC : C ≤ 1) : ∃ d n : Nat, 1 ≤ d ∧ 1 ≤ n ∧ C < (hapSum f d n).natAbs := by
  obtain ⟨d, n, hd, hn, hlt⟩ := erdos_discrepancy f hf
  exact ⟨d, n, hd, hn, by omega⟩

/-- The explicit `±1` sequence `+ - - + - + + - - + +` (extended by `1` beyond index
`11`), used to show that the bound `12` in `Frontier.erdos_discrepancy_uniform` is
optimal. -/
