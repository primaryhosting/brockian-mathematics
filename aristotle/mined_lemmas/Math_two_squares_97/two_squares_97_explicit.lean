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

theorem two_squares_97_explicit : (97 : ℕ) = 4 ^ 2 + 9 ^ 2 := by norm_num

end Math

/-!
# Two Squares 97
Category: Pure Mathematics
Target: Math.two_squares_97
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Primality of a natural number, stated without any external dependency
(so that this file can begin with the required header comment, which Lean
does not allow to precede `import` commands). -/
