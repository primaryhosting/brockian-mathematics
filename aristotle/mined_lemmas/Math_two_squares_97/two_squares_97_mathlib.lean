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

theorem two_squares_97_mathlib : Nat.Prime 97 ∧ ∃ a b : ℕ, a ^ 2 + b ^ 2 = 97 := by
  haveI : Fact (Nat.Prime 97) := ⟨by norm_num⟩
  exact ⟨by norm_num, Nat.Prime.sq_add_sq (by norm_num)⟩

/-- The explicit witness: `97 = 4 ^ 2 + 9 ^ 2`. -/
