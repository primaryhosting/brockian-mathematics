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

noncomputable def mirzRHS05 (L : Fin 5 → ℝ) : ℝ :=
  (1 / 2) * ∑ k : Fin 6, (∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ),
      x * y * mirzKernel (x + y) (L 0) *
        V03 (Fin.cons x (fun m => L ((split05 k).1 m))) *
        V03 (Fin.cons y (fun m => L ((split05 k).2 m))))
  + (1 / 2) * ∑ j ∈ ({1, 2, 3, 4} : Finset (Fin 5)),
      ∫ x in Ioi (0:ℝ), x * (mirzKernel x (L 0 + L j) + mirzKernel x (L 0 - L j)) *
        V04 (Fin.cons x (fun m => L (rest05 j m)))

