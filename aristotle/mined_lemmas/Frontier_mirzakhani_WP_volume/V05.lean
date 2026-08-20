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

noncomputable def V05 (L : Fin 5 → ℝ) : ℝ :=
  (∑ i, (L i) ^ 2) ^ 2 / 4 - (∑ i, (L i) ^ 4) / 8 + 3 * π ^ 2 * (∑ i, (L i) ^ 2) + 10 * π ^ 4

/-! ## One-dimensional (`B`-type) terms -/

