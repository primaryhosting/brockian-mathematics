import Mathlib
import RequestProject.TwoSquares29

/-!
Mathlib-facing restatement of `Math.two_squares_29`: the predicate `Math.IsPrimeNat` used in
`RequestProject/TwoSquares29.lean` agrees with Mathlib's `Nat.Prime`, so `29` is a Mathlib-prime
which is a sum of two squares.
-/

namespace Math


def IsPrimeNat (p : Nat) : Prop := 2 ≤ p ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

/-- `29` is prime. -/
