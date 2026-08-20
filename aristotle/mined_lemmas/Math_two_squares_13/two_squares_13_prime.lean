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

theorem two_squares_13_prime : Nat.Prime 13 ∧ ∃ a b : ℕ, 13 = a ^ 2 + b ^ 2 :=
  ⟨thirteen_prime_mathlib, two_squares_13⟩

end Math

/-!
# Two Squares 13
Category: Pure Mathematics
Target: Math.two_squares_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 13.** The prime `13` is a sum of two squares: `13 = 2 ^ 2 + 3 ^ 2`. -/
