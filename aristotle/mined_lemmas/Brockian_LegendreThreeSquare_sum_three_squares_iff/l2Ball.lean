import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

def l2Ball (r : ℝ) : Set E3 :=
  (WithLp.toLp (2 : ℝ≥0∞)) ⁻¹' Metric.ball (0 : E3L2) r

