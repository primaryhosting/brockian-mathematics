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

def ErdosDiscrepancyFinite : Prop :=
  ∀ C : ℕ, ∃ N : ℕ, ∀ f : ℕ → ℤ, IsPlusMinusOne f →
    ∃ d n : ℕ, 1 ≤ d ∧ 1 ≤ n ∧ n * d ≤ N ∧ C < (hapSum f d n).natAbs

/-- The `±1` sequence attached to a point of Cantor space. -/
