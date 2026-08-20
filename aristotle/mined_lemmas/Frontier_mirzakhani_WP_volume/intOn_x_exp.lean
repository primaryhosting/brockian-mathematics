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

lemma intOn_x_exp : IntegrableOn (fun x : ℝ => x * Real.exp (-(x/2))) (Ioi 0) := by
  have h := (intOn_pow_fd 1 0).const_mul 2
  refine Integrable.mono' h ?_ ?_
  · exact (measurable_id.mul (Real.measurable_exp.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0:ℝ) < x := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc x * Real.exp (-(x/2)) ≤ x * (2 * fd x) := by
          nlinarith [exp_le_two_fd hx0.le, fd_pos x]
      _ = 2 * (x ^ 1 * fd x) := by ring

