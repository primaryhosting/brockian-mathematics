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

def split05 : Fin 6 → (Fin 2 → Fin 5) × (Fin 2 → Fin 5) :=
  ![(![1, 2], ![3, 4]), (![1, 3], ![2, 4]), (![1, 4], ![2, 3]),
    (![3, 4], ![1, 2]), (![2, 4], ![1, 3]), (![2, 3], ![1, 4])]

/-- For `j ∈ {1,2,3,4}`, `rest05 j` lists the three indices of `{1,2,3,4}` other than `j`. -/
