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

lemma fd_le_exp (s : ℝ) : fd s ≤ Real.exp (-(s/2)) := by
  have h1 : (0:ℝ) < 1 + Real.exp (s / 2) := by positivity
  rw [fd, div_le_iff₀ h1, Real.exp_neg]
  have hx : (0:ℝ) < Real.exp (s/2) := Real.exp_pos _
  rw [inv_mul_eq_div, le_div_iff₀ hx]
  nlinarith [hx]

/-! ## Integrability -/

/-- All moments of the shifted kernel converge on any half-line. -/
