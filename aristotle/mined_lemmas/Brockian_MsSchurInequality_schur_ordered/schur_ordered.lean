import Mathlib
namespace Brockian.MsSchurInequality

/-- Schur's inequality in the case of an ordered triple `z ≤ y ≤ x` with `0 ≤ z`. -/

lemma schur_ordered (x y z t : ℝ) (hz : 0 ≤ z) (hzy : z ≤ y) (hyx : y ≤ x) (ht : 0 < t) :
    0 ≤ x ^ t * (x - y) * (x - z) + y ^ t * (y - x) * (y - z) + z ^ t * (z - x) * (z - y) := by
  have hy : (0:ℝ) ≤ y := le_trans hz hzy
  have hxt : y ^ t ≤ x ^ t := Real.rpow_le_rpow hy hyx ht.le
  have hyt : (0:ℝ) ≤ y ^ t := Real.rpow_nonneg hy t
  have hzt : (0:ℝ) ≤ z ^ t := Real.rpow_nonneg hz t
  -- `(x - y) * (xᵗ(x - z) - yᵗ(y - z)) + zᵗ(x - z)(y - z)` is a sum of nonnegative terms.
  have key : y ^ t * (y - z) ≤ x ^ t * (x - z) :=
    mul_le_mul hxt (by linarith) (by linarith) (le_trans hyt hxt)
  nlinarith [mul_nonneg hzt (mul_nonneg (by linarith : (0:ℝ) ≤ x - z) (by linarith : (0:ℝ) ≤ y - z)),
    mul_nonneg (by linarith : (0:ℝ) ≤ x - y) (by linarith : (0:ℝ) ≤ x ^ t * (x - z) - y ^ t * (y - z))]

/-- Schur's inequality: for nonnegative reals x,y,z and t > 0,
    xᵗ(x−y)(x−z) + yᵗ(y−x)(y−z) + zᵗ(z−x)(z−y) ≥ 0. -/
