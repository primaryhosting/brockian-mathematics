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

theorem exists_witness_of_odd_lt_300 :
    ∀ n, n < 300 → 9 ≤ n → n % 2 = 1 →
      ∃ p, p < 40 ∧ IsPrime p ∧ IsPrime (n - 3 - p) ∧ p + 3 ≤ n := by
  decide

/-- **Base case.** Every odd `n` with `9 ≤ n ≤ 299` is a sum of three primes. -/
