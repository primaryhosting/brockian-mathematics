import Mathlib

/-!
# Two Squares 41 — Mathlib companion

`41` is prime, and the fact that it is a sum of two squares also follows from
Mathlib's Fermat two-squares theorem `Nat.Prime.sq_add_sq`: a prime `p` with
`p % 4 ≠ 3` is a sum of two squares.
-/

namespace Math

/-- `41` is prime and is a sum of two squares. -/

theorem prime_41_and_two_squares : Nat.Prime 41 ∧ ∃ a b : ℕ, (41 : ℕ) = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 4, 5, by norm_num⟩

/-- The existence statement derived from Mathlib's two-squares theorem
`Nat.Prime.sq_add_sq`. -/
