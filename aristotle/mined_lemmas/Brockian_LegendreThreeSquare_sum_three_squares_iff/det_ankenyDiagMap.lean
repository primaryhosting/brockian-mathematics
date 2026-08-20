import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma det_ankenyDiagMap (n q : ℝ) :
    LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q)
      = Real.sqrt (2 * q) * (1 : ℝ) * Real.sqrt n := by
  simp [GeometryOfNumbers.Minkowski.ankenyDiagMap, LinearMap.det_toLin', Matrix.det_diagonal, Fin.prod_univ_three]

