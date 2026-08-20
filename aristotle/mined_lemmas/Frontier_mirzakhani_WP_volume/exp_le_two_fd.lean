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

lemma exp_le_two_fd {x : ℝ} (hx : 0 ≤ x) : Real.exp (-(x/2)) ≤ 2 * fd x := by
  have hpos : (0:ℝ) < 1 + Real.exp (x/2) := by positivity
  have he : (1:ℝ) ≤ Real.exp (x/2) := Real.one_le_exp (by linarith)
  have key : 1 / Real.exp (x/2) ≤ 2 / (1 + Real.exp (x/2)) := by
    rw [div_le_div_iff₀ (Real.exp_pos _) hpos]; nlinarith
  rw [Real.exp_neg, fd]
  calc (Real.exp (x/2))⁻¹ = 1 / Real.exp (x/2) := (one_div _).symm
    _ ≤ 2 / (1 + Real.exp (x/2)) := key
    _ = 2 * (1 / (1 + Real.exp (x/2))) := by ring

