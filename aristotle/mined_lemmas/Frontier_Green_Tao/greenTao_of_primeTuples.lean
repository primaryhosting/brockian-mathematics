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

theorem greenTao_of_primeTuples (h : PrimeTuplesConjecture) : GreenTaoStatement := by
  intro k
  obtain ⟨n, hn⟩ := h (apTuple k) (admissible_apTuple k)
  refine ⟨n, Nat.factorial k, Nat.factorial_pos k, ?_⟩
  intro i hi
  exact hn _ (mem_apTuple.mpr ⟨i, hi, rfl⟩)

/-- **Unconditional base cases**: `199 + 210 i`, `i < 10`, is a 10-term arithmetic
progression of primes, so `PrimeAP k` holds for every `k ≤ 10`. -/
