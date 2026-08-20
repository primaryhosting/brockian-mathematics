import Mathlib
import RequestProject.Main

/-!
# Bridge to Mathlib's `Nat.Prime`

`RequestProject.Main` is import-free (so that the required header comment can be the very first
thing in the file, which Lean forbids for files containing `import` commands).  This file checks
that the elementary primality predicate `Frontier.IsPrime` used there is exactly Mathlib's
`Nat.Prime`, and restates the results of `RequestProject.Main` in Mathlib's vocabulary.
-/

namespace Frontier

/-- The elementary primality predicate used in `RequestProject.Main` agrees with Mathlib's
`Nat.Prime`. -/

theorem goldbachEven_iff :
    GoldbachEven ↔ ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  simp only [GoldbachEven, isPrime_iff_nat_prime, Nat.even_iff]

/-- **Base case, Mathlib form.** Every odd `n` with `9 ≤ n ≤ 299` is a sum of three primes. -/
