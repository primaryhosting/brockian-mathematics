import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma ankenyBallRadius_pow_three (n q : ℝ) (hnq : 0 ≤ n * q) :
    (GeometryOfNumbers.Minkowski.ankenyBallRadius n q) ^ 3 = 8 * (n * q) * Real.sqrt (n * q) := by
  -- `r = 2 * sqrt(n*q)` and `(2 * a)^3 = 8 * a^3`,
  -- then `a^3 = (a^2) * a = (n*q) * sqrt(n*q)` for `a = sqrt(n*q)`.
  have hsq : (Real.sqrt (n * q)) ^ 2 = n * q := by
    simpa [pow_two] using (Real.sq_sqrt hnq)
  calc
    (GeometryOfNumbers.Minkowski.ankenyBallRadius n q) ^ 3
        = (2 * Real.sqrt (n * q)) ^ 3 := by
            simp [GeometryOfNumbers.Minkowski.ankenyBallRadius]
    _ = 8 * (Real.sqrt (n * q) ^ 3) := by
          -- `(2*a)^3 = 8*a^3`
          ring
    _ = 8 * ((Real.sqrt (n * q) ^ 2) * Real.sqrt (n * q)) := by
          simp [pow_succ, mul_assoc]
    _ = 8 * ((n * q) * Real.sqrt (n * q)) := by
          simp [hsq]
    _ = 8 * (n * q) * Real.sqrt (n * q) := by ring


