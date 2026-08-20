import Mathlib
import RequestProject.Kernel
import RequestProject.TwoDim

/-!
# Weil–Petersson volume polynomials in low complexity

We record the Weil–Petersson volume polynomials `V_{0,3}`, `V_{0,4}` and `V_{0,5}`, the
right-hand sides of Mirzakhani's recursion in the cases `(g,n) = (0,4)` and `(0,5)`, and
verify the recursion in both cases, together with the fact that the recursion determines
the volume polynomial.
-/

open scoped BigOperators Real
open MeasureTheory Set Real

namespace Frontier

set_option maxHeartbeats 1000000

/-! ## The volume polynomials -/

/-- `V_{0,3} ≡ 1`: the moduli space of pairs of pants is a point. -/

theorem integral_pow_three_mul_fd : (∫ x in Ioi (0:ℝ), x ^ 3 * fd x) = 14 * π ^ 4 / 15 := by
  have h := integral_pow_mul_fd 3
  rw [integral_pow_three_div_one_add_exp] at h
  rw [h]
  norm_num
  ring


