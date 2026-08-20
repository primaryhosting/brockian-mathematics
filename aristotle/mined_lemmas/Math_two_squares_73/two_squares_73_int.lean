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

theorem two_squares_73_int : Prime (73 : ℤ) ∧ ∃ a b : ℤ, (73 : ℤ) = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 3, 8, by norm_num⟩

/-- The existence part, obtained instead from Fermat's two-squares theorem: since `73`
is prime and `73 % 4 ≠ 3`, it is a sum of two squares. -/
