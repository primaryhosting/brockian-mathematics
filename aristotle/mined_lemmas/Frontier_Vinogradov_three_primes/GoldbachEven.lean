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

def GoldbachEven : Prop :=
  ∀ n : Nat, 2 < n → n % 2 = 0 → ∃ p q : Nat, IsPrime p ∧ IsPrime q ∧ p + q = n

/-! ## A sufficient criterion -/

/-- If `p` and `n - 3 - p` are prime and `p + 3 ≤ n`, then `n = p + (n - 3 - p) + 3` is a sum of
three primes. -/
