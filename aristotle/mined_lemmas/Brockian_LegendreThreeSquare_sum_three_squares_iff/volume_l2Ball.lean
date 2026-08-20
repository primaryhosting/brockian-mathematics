import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma volume_l2Ball (r : ℝ) :
    volume (l2Ball r) = (ENNReal.ofReal r) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
  -- First: measure-preserving bridge says volume preimage = volume image ball.
  have hpre :
      volume (l2Ball r) = volume (Metric.ball (0 : E3L2) r) := by
    simpa [l2Ball] using
      (PiLp.volume_preserving_toLp (ι := Fin 3)).measure_preimage measurableSet_ball.nullMeasurableSet
  -- Second: explicit 3-ball volume.
  have hball :
      volume (Metric.ball (0 : E3L2) r) =
        (ENNReal.ofReal r) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) :=
    EuclideanSpace.volume_ball_fin_three (x := (0 : E3L2)) (r := r)
  simpa [hpre, hball]

