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

def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ m, m < p → 2 ≤ m → p % m ≠ 0

instance decidableIsPrime (p : Nat) : Decidable (IsPrime p) :=
  inferInstanceAs (Decidable (2 ≤ p ∧ ∀ m, m < p → 2 ≤ m → p % m ≠ 0))

