import Mathlib
namespace Brockian.MsSchurInequality

/-- Schur's inequality in the sorted case `0 ≤ z ≤ y ≤ x`. -/

private lemma schur_sorted (x y z t : ℝ) (hz : 0 ≤ z) (hzy : z ≤ y) (hyx : y ≤ x)
    (ht : 0 < t) :
    0 ≤ x ^ t * (x - y) * (x - z) + y ^ t * (y - x) * (y - z) + z ^ t * (z - x) * (z - y) := by
  have hy : (0:ℝ) ≤ y := le_trans hz hzy
  have hxy : y ^ t ≤ x ^ t := Real.rpow_le_rpow hy hyx ht.le
  have hzt : (0:ℝ) ≤ z ^ t := Real.rpow_nonneg hz t
  have hyt : (0:ℝ) ≤ y ^ t := Real.rpow_nonneg hy t
  have key : x ^ t * (x - y) * (x - z) + y ^ t * (y - x) * (y - z) + z ^ t * (z - x) * (z - y)
      = (x - y) * (x ^ t * (x - z) - y ^ t * (y - z)) + z ^ t * (x - z) * (y - z) := by ring
  rw [key]
  have h1 : 0 ≤ (x - y) * (x ^ t * (x - z) - y ^ t * (y - z)) := by
    refine mul_nonneg (by linarith) ?_
    have : y ^ t * (y - z) ≤ x ^ t * (x - z) :=
      mul_le_mul hxy (by linarith) (by linarith) (le_trans hyt hxy)
    linarith
  have h2 : 0 ≤ z ^ t * (x - z) * (y - z) :=
    mul_nonneg (mul_nonneg hzt (by linarith)) (by linarith)
  linarith

/-- Schur's inequality: for nonnegative reals x,y,z and t > 0,
    xᵗ(x−y)(x−z) + yᵗ(y−x)(y−z) + zᵗ(z−x)(z−y) ≥ 0. -/
