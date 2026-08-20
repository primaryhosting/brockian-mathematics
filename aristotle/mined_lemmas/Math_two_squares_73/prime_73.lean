import Mathlib
import RequestProject.TwoSquares73

/-!
# Two Squares 73, via Mathlib's Fermat two-squares theorem

Companion file to `RequestProject/TwoSquares73.lean`: it derives the same statement
from Mathlib's `Nat.Prime.sq_add_sq`, and records that `73` is indeed prime.
-/

namespace Math

/-- `73` is prime. -/

theorem prime_73 : Nat.Prime 73 := by norm_num

/-- The prime `73` is a sum of two squares, obtained from Mathlib's Fermat
two-squares theorem `Nat.Prime.sq_add_sq` using `73 % 4 = 1`. -/
