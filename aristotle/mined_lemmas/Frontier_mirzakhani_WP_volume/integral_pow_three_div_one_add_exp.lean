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

theorem integral_pow_three_div_one_add_exp :
    (∫ x in Ioi (0:ℝ), x ^ 3 / (1 + Real.exp x)) = 7 * π ^ 4 / 120 := by
  have h := integral_pow_div_one_add_exp 3 hasSum_alt_zeta_four
  rw [show ((3:ℕ).factorial : ℝ) = 6 from by norm_num] at h
  rw [h]
  ring

/-! ## Moments of `fd` -/

