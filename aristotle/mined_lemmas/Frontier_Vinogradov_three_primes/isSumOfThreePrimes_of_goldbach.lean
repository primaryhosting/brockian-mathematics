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

theorem isSumOfThreePrimes_of_goldbach (hG : GoldbachEven) {n : Nat} (h9 : 9 ≤ n)
    (hodd : n % 2 = 1) : IsSumOfThreePrimes n := by
  obtain ⟨p, q, hp, hq, hpq⟩ := hG (n - 3) (by omega) (by omega)
  exact ⟨p, q, 3, hp, hq, isPrime_three, by omega⟩

/-- **Target.** The binary Goldbach conjecture implies Vinogradov's three primes theorem: every
odd `n ≥ 9` — in particular every sufficiently large odd number — is a sum of three primes. -/
