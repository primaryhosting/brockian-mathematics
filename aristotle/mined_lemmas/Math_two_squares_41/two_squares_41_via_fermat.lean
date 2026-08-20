import Mathlib

/-!
# Two Squares 41 — Mathlib companion

`41` is prime, and the fact that it is a sum of two squares also follows from
Mathlib's Fermat two-squares theorem `Nat.Prime.sq_add_sq`: a prime `p` with
`p % 4 ≠ 3` is a sum of two squares.
-/

namespace Math

/-- `41` is prime and is a sum of two squares. -/

theorem two_squares_41_via_fermat : ∃ a b : ℕ, (41 : ℕ) = a ^ 2 + b ^ 2 := by
  haveI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  obtain ⟨a, b, h⟩ := Nat.Prime.sq_add_sq (p := 41) (by norm_num)
  exact ⟨a, b, h.symm⟩

end Math

/-!
# Two Squares 41
Category: Pure Mathematics
Target: Math.two_squares_41
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The prime `41` is a sum of two squares: `41 = 4 ^ 2 + 5 ^ 2`.

(The required header comment must be the first thing in this file, and Lean forbids
`import` after a module docstring, so this file is deliberately import-free and
self-contained. The companion file `RequestProject/TwoSquares41Mathlib.lean`
records the primality of `41` and derives the same existence statement from
Mathlib's Fermat two-squares theorem `Nat.Prime.sq_add_sq`.) -/
