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

lemma integral_x_mirzKernel_add (a b : ℝ) :
    (∫ x in Ioi (0:ℝ), x * (mirzKernel x a + mirzKernel x b)) = F1 a + F1 b := by
  have ha := intOn_pow_mirzKernel 1 a
  have hb := intOn_pow_mirzKernel 1 b
  simp only [pow_one] at ha hb
  rw [F1, F1, ← integral_add ha hb]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x _
  show x * (mirzKernel x a + mirzKernel x b) = x * mirzKernel x a + x * mirzKernel x b
  ring

/-- The `B`-term integral against an affine-in-`x²` volume factor. -/
