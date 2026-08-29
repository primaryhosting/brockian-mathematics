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

def PrimeTuplesConjecture : Prop :=
  ∀ B : Finset ℕ, Admissible B → ∃ n : ℕ, ∀ b ∈ B, Nat.Prime (n + b)

/-- The candidate tuple for a `k`-term arithmetic progression of primes:
`{0, W, 2W, …, (k-1)W}` with `W = k !`. -/
