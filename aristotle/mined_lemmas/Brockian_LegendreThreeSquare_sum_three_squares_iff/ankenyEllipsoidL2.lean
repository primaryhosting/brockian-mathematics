import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

def ankenyEllipsoidL2 (n q : ℝ) : Set E3 :=
  GeometryOfNumbers.Minkowski.ankenyDiagMap n q ⁻¹' l2Ball (GeometryOfNumbers.Minkowski.ankenyBallRadius n q)

