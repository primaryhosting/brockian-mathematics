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

lemma integral_shift_pow (m : ℕ) (d : ℝ) :
    (∫ x in Ioi (0:ℝ), x^m * fd (x + d)) = ∫ y in Ioi d, (y - d)^m * fd y := by
  have h := integral_Ioi_comp_add_right (fun y => (y - d)^m * fd y) 0 d
  simp only [zero_add] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx
  show x^m * fd (x + d) = (x + d - d)^m * fd (x + d)
  rw [add_sub_cancel_right]

