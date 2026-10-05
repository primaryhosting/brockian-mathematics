import Mathlib
import RequestProject.TwoSquares113

/-!
# Two Squares 113 (Mathlib restatement)

Restatement of `Math.two_squares_113` using Mathlib's `Nat.Prime`.
-/

namespace Math

/-- `Math.IsPrimeNat` agrees with Mathlib's `Nat.Prime`. -/

def IsPrimeNat (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- The prime `113` is a sum of two squares: `113 = 7 ^ 2 + 8 ^ 2`. -/
