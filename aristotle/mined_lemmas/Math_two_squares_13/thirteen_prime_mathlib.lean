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

theorem thirteen_prime_mathlib : Nat.Prime 13 := by norm_num

/-- Existence of a two-square representation of `13`, obtained from Mathlib's
`Nat.Prime.sq_add_sq` (Fermat's two-squares theorem) rather than by exhibiting `2` and `3`. -/
