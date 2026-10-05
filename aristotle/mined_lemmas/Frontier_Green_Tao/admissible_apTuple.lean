import Mathlib

/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires every `import` command to appear before any other
command in a module, including module docstrings, so the mandated header comment appears
immediately after the single `import Mathlib` line.
-/

open scoped BigOperators

namespace Frontier

/-- `PrimeAP k` says that there is an arithmetic progression of length `k` with positive
common difference all of whose terms are prime. -/

theorem admissible_apTuple (k : ℕ) : Admissible (apTuple k) := by
  intro p hp
  by_cases h : p ≤ k
  · exact ⟨1, apTuple_avoid_small hp h⟩
  · exact apTuple_avoid_large hp (Nat.lt_of_not_le h)

/-- **Reduction**: the prime `k`-tuples conjecture implies the Green–Tao statement. -/
