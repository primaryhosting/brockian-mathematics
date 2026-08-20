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

lemma V04_cons (x : ℝ) (r : Fin 3 → ℝ) :
    V04 (Fin.cons x r) = (2 * π ^ 2 + (∑ m, (r m) ^ 2) / 2) + x ^ 2 / 2 := by
  have e0 : (Fin.cons x r : Fin 4 → ℝ) 0 = x := rfl
  have e1 : (Fin.cons x r : Fin 4 → ℝ) 1 = r 0 := rfl
  have e2 : (Fin.cons x r : Fin 4 → ℝ) 2 = r 1 := rfl
  have e3 : (Fin.cons x r : Fin 4 → ℝ) 3 = r 2 := rfl
  rw [V04, Fin.sum_univ_four, Fin.sum_univ_three, e0, e1, e2, e3]
  ring

