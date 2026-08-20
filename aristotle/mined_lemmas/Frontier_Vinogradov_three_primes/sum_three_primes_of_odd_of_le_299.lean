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

theorem sum_three_primes_of_odd_of_le_299 {n : ℕ} (h9 : 9 ≤ n) (hn : n ≤ 299) (hodd : Odd n) :
    ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n :=
  (isSumOfThreePrimes_iff n).mp
    (isSumOfThreePrimes_of_odd_of_le_299 h9 hn (Nat.odd_iff.mp hodd))

/-- **Target, Mathlib form.** The binary Goldbach conjecture implies that every sufficiently large
odd number is a sum of three primes. -/
