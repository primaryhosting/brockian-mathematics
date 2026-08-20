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

theorem isSumOfThreePrimes_iff (n : ℕ) :
    IsSumOfThreePrimes n ↔ ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n := by
  simp only [IsSumOfThreePrimes, isPrime_iff_nat_prime]

/-- `Frontier.GoldbachEven` is exactly the binary Goldbach conjecture, stated with Mathlib's
`Nat.Prime` and `Even`. -/
