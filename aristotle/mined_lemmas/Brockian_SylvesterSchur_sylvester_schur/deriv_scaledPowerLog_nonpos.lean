import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma deriv_scaledPowerLog_nonpos {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hmain : √y * (2 + log y) ≤ 2 * x) :
    deriv (fun t => scaledPowerLog x t) y ≤ 0 := by
  have hderiv := (hasDerivAt_scaledPowerLog (x := x) (y := y) hx hy).deriv
  rw [hderiv]
  have hsqrt_pos : 0 < √y := sqrt_pos_of_pos hy
  rw [sub_nonpos]
  rw [div_le_div_iff₀ (mul_pos two_pos hsqrt_pos) hy]
  nlinarith [sq_sqrt hy.le]

