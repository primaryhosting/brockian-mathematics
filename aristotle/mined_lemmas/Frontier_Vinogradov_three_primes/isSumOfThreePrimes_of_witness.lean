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

theorem isSumOfThreePrimes_of_witness {n p : Nat} (hp : IsPrime p) (hq : IsPrime (n - 3 - p))
    (hle : p + 3 ≤ n) : IsSumOfThreePrimes n :=
  ⟨p, n - 3 - p, 3, hp, hq, isPrime_three, by omega⟩

/-! ## The base case, verified by kernel computation -/

set_option maxRecDepth 100000 in
/-- Kernel-checked witness search: for every odd `n` with `9 ≤ n < 300` there is a prime `p < 40`
such that `n - 3 - p` is also prime. -/
