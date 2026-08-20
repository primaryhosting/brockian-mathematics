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

theorem isSumOfThreePrimes_of_odd_of_le_299 {n : Nat} (h9 : 9 ≤ n) (hn : n ≤ 299)
    (hodd : n % 2 = 1) : IsSumOfThreePrimes n := by
  obtain ⟨p, -, hp, hq, hle⟩ := exists_witness_of_odd_lt_300 n (by omega) h9 hodd
  exact isSumOfThreePrimes_of_witness hp hq hle

/-! ## The reduction to the binary Goldbach conjecture -/

/-- **Reduction.** Assuming the binary Goldbach conjecture, every odd `n ≥ 9` is a sum of three
primes: write `n = 3 + (n - 3)`, where `n - 3` is even and greater than `2`. -/
