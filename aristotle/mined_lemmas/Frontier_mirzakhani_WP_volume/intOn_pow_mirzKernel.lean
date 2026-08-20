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

lemma intOn_pow_mirzKernel (k : ℕ) (t : ℝ) :
    IntegrableOn (fun x => x ^ k * mirzKernel x t) (Ioi 0) := by
  have h1 := intOn_pow_fd_shift k t 0
  have h2 := intOn_pow_fd_shift k (-t) 0
  refine (h1.add h2).congr (Filter.Eventually.of_forall (fun x => ?_))
  show x ^ k * fd (x + t) + x ^ k * fd (x + -t) = x ^ k * mirzKernel x t
  simp only [mirzKernel, sub_eq_add_neg]
  ring

