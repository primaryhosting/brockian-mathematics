import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

def ankenyBallRadius (n q : ℝ) : ℝ :=
  2 * Real.sqrt (n * q)

