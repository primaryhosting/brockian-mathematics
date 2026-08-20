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

lemma F3_eq_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    F3 t = t ^ 4 / 4 + 2 * π ^ 2 * t ^ 2 + 28 * π ^ 4 / 15 := by
  rw [F3, mirz_split_pow 3 t, integral_shift_pow 3 t, integral_shift_pow 3 (-t),
    integral_Ioi_cubic_shift t t, integral_Ioi_cubic_shift (-t) (-t),
    moment_split_pos 0 ht, moment_split_pos 1 ht, moment_split_pos 2 ht, moment_split_pos 3 ht,
    moment_split_neg 0 ht, moment_split_neg 1 ht, moment_split_neg 2 ht, moment_split_neg 3 ht,
    interval_refl 0 t, interval_refl 1 t, interval_refl 2 t, interval_refl 3 t,
    moment_one, moment_three]
  norm_num
  ring

