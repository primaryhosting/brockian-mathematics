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

def rest05 : Fin 5 → Fin 3 → Fin 5 :=
  ![![2, 3, 4], ![2, 3, 4], ![1, 3, 4], ![1, 2, 4], ![1, 2, 3]]

/-- The right-hand side of Mirzakhani's recursion for `(g,n) = (0,5)`: the separating
term (a sum over the six ordered splittings of the remaining boundary components into
two pairs, each contributing a product `V_{0,3} · V_{0,3}`) plus the `B`-term (a sum
over the four remaining boundary components, each contributing a `V_{0,4}`).  The
non-separating term is absent in genus `0`. -/
