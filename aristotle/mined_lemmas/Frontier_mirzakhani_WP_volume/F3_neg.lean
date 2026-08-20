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

lemma F3_neg (t : ℝ) : F3 (-t) = F3 t := by
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx
  simp only [mirzKernel, sub_neg_eq_add, ← sub_eq_add_neg]
  ring

/-- **Mirzakhani's first integral transform.**  `∫₀^∞ x H(x,t) dx = t²/2 + 2π²/3`. -/
