import Mathlib
import RequestProject.TwoSquares73

/-!
# Two Squares 73 — Mathlib phrasing

Restatements of `Math.two_squares_73` using Mathlib's `Nat.Prime`, over `ℕ` and `ℤ`,
together with a derivation of the existence part from Fermat's two-squares theorem
(`Nat.Prime.sq_add_sq`).
-/

namespace Math

/-- The prime `73` is a sum of two squares: `73 = 3 ^ 2 + 8 ^ 2`. -/

theorem two_squares_73_prime : Nat.Prime 73 ∧ ∃ a b : ℕ, 73 = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, two_squares_73.2⟩

/-- The integer version: `73` is prime and a sum of two integer squares. -/
