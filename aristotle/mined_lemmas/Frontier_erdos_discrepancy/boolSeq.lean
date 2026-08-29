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

def boolSeq (g : ℕ → Bool) : ℕ → ℤ := fun n => if g n then 1 else -1

