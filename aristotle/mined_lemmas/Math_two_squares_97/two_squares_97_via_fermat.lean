import Mathlib
import RequestProject.TwoSquares97

/-!
# Two Squares 97, via Fermat's two-squares theorem

A Mathlib-based derivation of `Math.two_squares_97`, using
`Nat.Prime.sq_add_sq`.
-/

namespace Math

/-- `97` is a sum of two squares, derived from Mathlib's Fermat two-squares
theorem `Nat.Prime.sq_add_sq`. -/

theorem two_squares_97_via_fermat : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 97 :=
  haveI : Fact (Nat.Prime 97) := ⟨by norm_num⟩
  Nat.Prime.sq_add_sq (p := 97) (by norm_num)

end Math

/-!
# Two Squares 97
Category: Pure Mathematics
Target: Math.two_squares_97
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The prime `97` is a sum of two squares: `97 = 9 ^ 2 + 4 ^ 2`.

This file is deliberately import-free so that the required header comment can be
the very first thing in the file (Lean requires `import` lines to precede all
other commands, including module docstrings).  A derivation of the same
statement from Mathlib's Fermat two-squares theorem `Nat.Prime.sq_add_sq`
(`p.Prime → p % 4 ≠ 3 → ∃ a b, a ^ 2 + b ^ 2 = p`, applicable since `97 % 4 = 1`)
is given in `RequestProject.TwoSquares97Fermat`. -/
