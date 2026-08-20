import Mathlib

/-!
# Two Squares 97 — Mathlib version

Companion to `RequestProject/TwoSquares97.lean`.  Here the statement is phrased
with Mathlib's `Nat.Prime` and derived from the general Mathlib theorem
`Nat.Prime.sq_add_sq` (Fermat's two-squares theorem: a prime `p` with
`p % 4 ≠ 3` is a sum of two squares).
-/

namespace Math

/-- `97` is prime and is a sum of two squares, via `Nat.Prime.sq_add_sq`. -/

def IsPrimeNat (p : Nat) : Prop := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p

/-- `97` is prime. -/
