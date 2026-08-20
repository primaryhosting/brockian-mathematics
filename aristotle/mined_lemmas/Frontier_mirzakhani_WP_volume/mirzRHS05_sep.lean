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

lemma mirzRHS05_sep (L : Fin 5 → ℝ) (k : Fin 6) :
    (∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ),
      x * y * mirzKernel (x + y) (L 0) *
        V03 (Fin.cons x (fun m => L ((split05 k).1 m))) *
        V03 (Fin.cons y (fun m => L ((split05 k).2 m)))) = F3 (L 0) / 6 := by
  rw [← integral_quadrant_mirzKernel (L 0)]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x _
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro y _
  show x * y * mirzKernel (x + y) (L 0) *
      V03 (Fin.cons x (fun m => L ((split05 k).1 m))) *
      V03 (Fin.cons y (fun m => L ((split05 k).2 m)))
    = x * y * mirzKernel (x + y) (L 0)
  rw [show V03 (Fin.cons x (fun m => L ((split05 k).1 m))) = 1 from rfl,
    show V03 (Fin.cons y (fun m => L ((split05 k).2 m))) = 1 from rfl]
  ring

