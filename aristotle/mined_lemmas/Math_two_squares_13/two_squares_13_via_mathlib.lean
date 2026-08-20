import Mathlib
import RequestProject.TwoSquares13

/-
# Two Squares 13 — Mathlib version

Companion to `RequestProject/TwoSquares13.lean`.  (That file must literally begin with the
prescribed module-doc header, and Lean 4 does not allow `import` commands after a doc comment,
so the Mathlib-based development lives here.)

The relevant Mathlib result is `Nat.Prime.sq_add_sq` (Mathlib/NumberTheory/SumTwoSquares.lean):
for a prime `p` with `p % 4 ≠ 3` there are naturals `a b` with `a ^ 2 + b ^ 2 = p`.
-/

namespace Math

/-- `13` is prime, in Mathlib's sense. -/

theorem two_squares_13_via_mathlib : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 13 :=
  haveI : Fact (Nat.Prime 13) := ⟨thirteen_prime_mathlib⟩
  Nat.Prime.sq_add_sq (p := 13) (by decide)

/-- The explicit statement `Math.two_squares_13`, restated with `Nat.Prime`. -/
