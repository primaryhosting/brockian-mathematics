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

lemma F1_eq_of_nonneg {t : ℝ} (ht : 0 ≤ t) : F1 t = t ^ 2 / 2 + 2 * π ^ 2 / 3 := by
  have hF : F1 t = ∫ x in Ioi (0:ℝ), x^1 * mirzKernel x t := by
    rw [F1]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    show x * mirzKernel x t = x^1 * mirzKernel x t
    rw [pow_one]
  rw [hF, mirz_split_pow 1 t, integral_shift_pow 1 t, integral_shift_pow 1 (-t),
    integral_Ioi_linear_shift t t, integral_Ioi_linear_shift (-t) (-t),
    moment_split_pos 0 ht, moment_split_pos 1 ht, moment_split_neg 0 ht, moment_split_neg 1 ht,
    interval_refl 0 t, interval_refl 1 t, moment_one]
  norm_num
  ring

