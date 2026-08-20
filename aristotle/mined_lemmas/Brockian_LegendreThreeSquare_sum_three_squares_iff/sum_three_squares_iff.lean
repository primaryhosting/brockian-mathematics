import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

theorem sum_three_squares_iff (n : ℕ) :
    (∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) ↔ ¬ is_three_square_exception n := by
  constructor
  · intro h
    exact not_exception_of_sum_three_squares n h
  · intro h
    exact sum_three_squares_of_not_exception n h

end GeometryOfNumbers
import Mathlib.Data.Nat.Basic

namespace GeometryOfNumbers
/-!
# Three-Square Exceptions

This file defines the set of integers that cannot be represented as a sum of three squares.

## Mathematical Definition
A positive integer \(n\) is a three-square exception if and only if it is of the form \(4^a(8k + 7)\) for some integers \(a, k \ge 0\).
-/

