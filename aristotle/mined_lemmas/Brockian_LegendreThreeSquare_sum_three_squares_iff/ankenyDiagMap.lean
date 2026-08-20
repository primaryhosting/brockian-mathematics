import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

def ankenyDiagMap (n q : ℝ) : E3 →ₗ[ℝ] E3 :=
  Matrix.toLin' (Matrix.diagonal ![Real.sqrt (2 * q), (1 : ℝ), Real.sqrt n])

