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

def Admissible (B : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ n : ℕ, ∀ b ∈ B, ¬ (p ∣ n + b)

/-- The (existence form of the) Hardy–Littlewood / Dickson prime `k`-tuples conjecture:
every admissible finite set `B` admits a shift `n` making all of `n + b`, `b ∈ B`, prime.
This is weaker than the usual statement, which asserts infinitely many such `n`. -/
