import Mathlib
namespace Brockian.MsSchurInequality
/-- Schur's inequality: for nonnegative reals x,y,z and t > 0,
    xᵗ(x−y)(x−z) + yᵗ(y−x)(y−z) + zᵗ(z−x)(z−y) ≥ 0. -/
theorem schur_inequality (x y z t : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (ht : 0 < t) :
    0 ≤ x ^ t * (x - y) * (x - z) + y ^ t * (y - x) * (y - z) + z ^ t * (z - x) * (z - y) := by
  sorry
end Brockian.MsSchurInequality
