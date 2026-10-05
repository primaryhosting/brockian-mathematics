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

lemma mem_apTuple {k b : ℕ} : b ∈ apTuple k ↔ ∃ i < k, i * Nat.factorial k = b := by
  simp [apTuple, Finset.mem_image, Finset.mem_range]

/-- Small primes: a prime `p ≤ k` divides `k !`, so the tuple lies in the class `0 mod p`
and the shift `n = 1` works. -/
