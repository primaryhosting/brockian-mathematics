import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

def is_three_square_exception (n : ℕ) : Prop :=
  ∃ a k : ℕ, n = 4 ^ a * (8 * k + 7)

end GeometryOfNumbers
