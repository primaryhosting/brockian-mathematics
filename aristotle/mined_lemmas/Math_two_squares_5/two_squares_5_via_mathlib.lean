import Mathlib
import RequestProject.TwoSquares5

/-!
# Two Squares 5 — via Mathlib's two-squares theorem

The target theorem `Math.two_squares_5` lives in `RequestProject/TwoSquares5.lean`, which
(because the required file header must be the very first thing in that file, before any
`import`) is import-free and proves the statement by direct computation.

Here we record the same fact as an instance of Mathlib's Fermat two-squares theorem
`Nat.Prime.sq_add_sq`: every prime `p` with `p % 4 ≠ 3` is a sum of two squares.
-/

namespace Math

/-- `5` is a sum of two squares, obtained from `Nat.Prime.sq_add_sq` since `5` is prime
and `5 % 4 = 1 ≠ 3`. -/

theorem two_squares_5_via_mathlib : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 5 :=
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  Nat.Prime.sq_add_sq (p := 5) (by norm_num)

end Math

/-!
# Two Squares 5
Category: Pure Mathematics
Target: Math.two_squares_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The prime `5` is a sum of two squares: `5 = 1 ^ 2 + 2 ^ 2`. -/
